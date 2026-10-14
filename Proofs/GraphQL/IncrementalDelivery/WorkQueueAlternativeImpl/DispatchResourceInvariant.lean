import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.TaskRecordPreservation

/-! Compose existing and incoming task/source representation at one actual dispatch.
Acquisition inventories and native structural identity remain independent audit evidence.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- One before-state invariant supplies both records and task completion history
-----------------------------------------------------------------------------------------

/-- Actual acquired queue leases have current records, and computation leases are pending.
The task history is proof notation; ports need not keep a production completion ledger.
-/
def QueueResourcesRepresented (queue : ReferenceWorkQueue.State)
    (settled : List WorkQueueSemantics.Occurrence) (resources : ResourceState)
    : Prop :=
  TasksPendingRepresented queue settled resources ∧ SourcesRepresented queue resources

/-- Task/source locations together represent every independently acquired queue lease. -/
theorem QueueResourcesRepresented.records {queue settled resources}
    (represented : QueueResourcesRepresented queue settled resources)
    : ResourcesRepresented queue resources := by
  intro target owned
  cases target with
  | task occurrence => exact (represented.1 occurrence owned).1
  | stream key => exact represented.2 key owned

-----------------------------------------------------------------------------------------
-- Full dispatch construction uses the same input, native inventory and observer
-----------------------------------------------------------------------------------------

/-- All five handlers preserve acquired queue-lease representation and genuine pending
task history. Only incoming native structural identity and the before invariant are inputs;
neither desired endpoint coverage nor disposal effects nor native completeness is assumed.
-/
def GeneratedDispatchResourcesRepresented : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories),
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        QueueResourcesRepresented before.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources
        → ProducerTasksMatchWork work resources inventories
            (graphEffects before.queue event)
        → ProducerSourcesMatchWork work resources inventories
            (graphEffects before.queue event)
        → QueueResourcesRepresented reduced.state.queue
            (event.recordTaskOutcome
              (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten))
            (resources.observeDispatch inventories before event).1

/-- Checked composition of independently proved task and source constructions. -/
theorem GeneratedDispatchResourcesRepresented_holds
    : GeneratedDispatchResourcesRepresented := by
  intro work inputs event generated valid started resources inventories
  dsimp only
  intro represented taskIdentity sourceIdentity
  exact ⟨GeneratedDispatchTasksPendingRepresented_holds work inputs event generated valid started
    resources inventories represented.1 taskIdentity,
    GeneratedDispatchSourcesRepresented_holds work inputs event generated valid started
      resources inventories represented.2 sourceIdentity⟩

/-- The full observer constructs a compatible legal history and actual endpoint records.
This is a model dispatch theorem, not construction of complete native acquisition evidence.
-/
theorem generatedDispatch_resourceReplay_and_records
    {work inputs event resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (represented
      : QueueResourcesRepresented ((State.initialize work).runNormalized inputs).1.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources)
    (taskIdentity
      : ProducerTasksMatchWork work resources inventories
          (graphEffects ((State.initialize work).runNormalized inputs).1.queue event))
    (sourceIdentity
      : ProducerSourcesMatchWork work resources inventories
          (graphEffects ((State.initialize work).runNormalized inputs).1.queue event))
    : let before := ((State.initialize work).runNormalized inputs).1
      let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
      let observed := resources.observeDispatch inventories before event
      ResourceReplay resources observed.2 observed.1
      ∧ ResourcesRepresented reduced.state.queue observed.1 :=
  ⟨
    resources.observeDispatch_replay inventories _ _,
    (GeneratedDispatchResourcesRepresented_holds work inputs event generated valid started
      resources inventories represented taskIdentity sourceIdentity).records
  ⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
