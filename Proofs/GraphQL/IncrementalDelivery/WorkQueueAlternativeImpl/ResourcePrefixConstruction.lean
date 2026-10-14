import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FIFOResourceInvariant
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RepresentedStopSafety

/-! Construct one actual finite arbitrary-width FIFO ownership history, including independent
initial acquisition, inter-input observations and terminal clearing. This is not the native
code-to-observation bridge or an implicit native acquisition inventory.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Separate immutable identity and independent acquisition from constructed coverage
-----------------------------------------------------------------------------------------

/-- A proof-side trace builds actual prefixes, not desired endpoint or stop laws. Initial
acquisition and inter-input callbacks are independent legal observations; each real dispatch
supplies only incoming structural identities and the unchanged source/start premises.
Batch identity evidence names each real FIFO handoff without restricting batch width.
-/
inductive ResourcePrefixConstruction (work : Work)
    : List (List GraphEvent) → ResourceState → List ResourceAction → Prop where
  | initial (resources : ResourceState) (actions : List ResourceAction)
    (acquired : ResourceReplay ResourceState.empty actions resources)
    (identities : InitialResourcesMatchWork work resources)
    : ResourcePrefixConstruction work [] resources actions
  | appendBatch {inputs resources actions}
    (earlier : ResourcePrefixConstruction work inputs resources actions)
    (batch : List GraphEvent) (inventories : ProducerInventories)
    (acquired : ResourceState) (externalActions : List ResourceAction)
    (externalReplay : ResourceReplay resources externalActions acquired)
    (externalOnly : ∀ action ∈ externalActions, InterInputResourceAction action)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (identities
      : BatchProducerIdentities work
          {
            dispatch := { state := ((State.initialize work).runNormalized inputs).1 },
            resources := acquired
          }
          inventories batch)
    : ResourcePrefixConstruction work (inputs ++ [batch])
        (State.observeResourceBatch ((State.initialize work).runNormalized inputs).1
          acquired inventories batch).resources
        (actions
          ++ externalActions
          ++ (State.observeResourceBatch ((State.initialize work).runNormalized inputs).1
                acquired inventories batch).actions)

/-- Preserve the singleton convenience interface using the general FIFO constructor. -/
theorem ResourcePrefixConstruction.append {work inputs resources actions}
    (earlier : ResourcePrefixConstruction work inputs resources actions)
    (event : GraphEvent) (inventories : ProducerInventories)
    (acquired : ResourceState) (externalActions : List ResourceAction)
    (externalReplay : ResourceReplay resources externalActions acquired)
    (externalOnly : ∀ action ∈ externalActions, InterInputResourceAction action)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (taskIdentity
      : ProducerTasksMatchWork work acquired inventories
          (graphEffects ((State.initialize work).runNormalized inputs).1.queue event))
    (sourceIdentity
      : ProducerSourcesMatchWork work acquired inventories
          (graphEffects ((State.initialize work).runNormalized inputs).1.queue event))
    : ResourcePrefixConstruction work (inputs ++ [[event]])
        (State.observeResourceBatch ((State.initialize work).runNormalized inputs).1
          acquired inventories [event]).resources
        (actions
          ++ externalActions
          ++ (State.observeResourceBatch ((State.initialize work).runNormalized inputs).1
                acquired inventories [event]).actions) := by
  apply earlier.appendBatch [event] inventories acquired externalActions externalReplay
    externalOnly valid started
  intro earlierEvents input suffix partition
  have length := congrArg List.length partition
  simp only [List.length_append, List.length_cons, List.length_nil] at length
  have empty : earlierEvents = [] := List.length_eq_zero_iff.mp (by omega)
  subst earlierEvents
  have same : input = event := (List.cons.inj partition).1.symm
  subst input
  exact ⟨taskIdentity, sourceIdentity⟩

-----------------------------------------------------------------------------------------
-- Construct history, records and terminal coverage together at the same prefix
-----------------------------------------------------------------------------------------

/-- Source validity and executable-start evidence are already carried by the real construction.
No final endpoint safety or stronger admission premise is needed to recover them.
-/
theorem ResourcePrefixConstruction.sourceEvidence {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
      ∧ ReferenceWorkQueue.inputsStarted work inputs = true := by
  cases built with
  | initial => exact ⟨.nil, rfl⟩
  | appendBatch earlier batch inventories acquired externalActions externalReplay
      externalOnly valid started identities =>
      exact ⟨
        by simpa only [List.flatten_append, List.flatten_cons,
          List.flatten_nil, List.append_nil] using valid,
        started
      ⟩

/-- Every built prefix has one compatible acquisition/completion/cleanup history and
actual record/pending-history coverage. A stopped endpoint has no queue-owned remainder.
Inventory completeness and native callback correspondence are not
replaced by this conditional construction.
-/
theorem ResourcePrefixConstruction.invariants {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    : ResourceReplay ResourceState.empty actions resources
      ∧ QueueResourcesRepresented ((State.initialize work).runNormalized inputs).1.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources
      ∧ (((State.initialize work).runNormalized inputs).1.stopped = true
          → ∀ target, resources target ≠ .owned .queue) := by
  induction built with
  | initial resources actions acquired identities =>
      refine ⟨acquired, GeneratedInitialResourcesRepresented_holds work generated resources identities, ?_⟩
      intro stopped
      change (State.initialize work).stopped = true at stopped
      rw [State.initialize_stopped] at stopped
      cases stopped
  | @appendBatch inputs resources actions earlier batch inventories acquired externalActions
      externalReplay externalOnly valid started identities ih =>
      have current := ih.2.1.interInputReplay externalReplay externalOnly
      obtain ⟨replay, represented, noOwned⟩ := GeneratedResourceBatchInvariant_holds work inputs batch
        generated valid started acquired inventories current identities
      have same := State.observeResourceBatch_state ((State.initialize work).runNormalized inputs).1
        acquired inventories batch
      rw [← State.runNormalized_append_state] at same
      have settled : ReferenceWorkQueue.GraphEvent.taskSettlements (inputs ++ [batch]).flatten
          = ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch) := by
        simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      refine ⟨(ih.1.append externalReplay).append replay, ?_, ?_⟩
      · rw [settled]
        exact same ▸ represented
      · exact same ▸ noOwned

/-- Every acquisition observed anywhere in a constructed history remains accounted for.
This does not manufacture native acquisitions or falsely settle requested cleanup.
-/
theorem ResourcePrefixConstruction.acquisition_accounted {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    {target owner} (acquired : ResourceAction.acquire target owner ∈ actions)
    : resources target ≠ .unacquired :=
  (built.invariants generated).1.acquisition_accounted acquired

/-- Actual stop coverage follows from constructed records at the same source prefix.
It is derived evidence for the native audit, not a caller-supplied coverage requirement.
-/
theorem ResourcePrefixConstruction.stopCoverage {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    : StopCoverage ((State.initialize work).runNormalized inputs).1 resources :=
  generatedReplay_stopCoverage_of_representation generated built.sourceEvidence.1
    built.sourceEvidence.2 resources (built.invariants generated).2.1.records

/-- Record representation entails the independently proved actual stop coverage reduction.
Generated source/start evidence belongs to this same prefix, not an unrelated legal run.
-/
theorem ResourcePrefixConstruction.stopSafety {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    (running : ((State.initialize work).runNormalized inputs).1.stopped = false)
    : let state := ((State.initialize work).runNormalized inputs).1
      ResourceReplay ResourceState.empty (actions ++ (resources.observeStop state).2)
        (resources.observeStop state).1
      ∧ ∀ target, (resources.observeStop state).1 target ≠ .owned .queue := by
  obtain ⟨replay, represented, _⟩ := built.invariants generated
  obtain ⟨stopped, noOwned⟩ := GeneratedRepresentedStopSafety_holds work inputs generated valid started resources
    represented.records running
  exact ⟨replay.append stopped, noOwned⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
