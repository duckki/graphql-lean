import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableSourceStartup

/-! Source records through direct task-failure settlement and its actual owner-removal fold.
Changing the rejected computation's diagnostic slot does not erase a held source's value.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

private theorem failureStep_sourceRecord (errors : Nat)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode) {key}
    : let next := fusedFailureGroupStep errors acc group
      acc.2.2.Subset next.2.2
      ∧ (RecordTargetRepresented acc.1.queue (.stream key)
          → RecordTargetRepresented next.1.queue (.stream key)
            ∨ .stream key ∈ next.2.2) := by
  unfold fusedFailureGroupStep
  split
  · exact ⟨List.Subset.refl _, fun represented => .inl represented⟩
  · split
    · rename_i node found active
      exact ⟨(FusedRemovalSafety_holds acc.1 node.group.node.ref acc.2.2).1,
        fun represented => sourceRecord_removeGroup acc.1 node.group.node.ref acc.2.2 represented⟩
    · exact ⟨List.Subset.refl _, fun represented => .inl represented⟩

/-- The same failure fold retains a source record or its cumulative inline cleanup target. -/
theorem sourceRecord_failureFold (errors : Nat) (groups : List Execution.DeliveryNode)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget) {key}
    (prior : RecordTargetRepresented acc.1.queue (.stream key) ∨ .stream key ∈ acc.2.2)
    : let next := groups.foldl (fusedFailureGroupStep errors) acc
      RecordTargetRepresented next.1.queue (.stream key) ∨ .stream key ∈ next.2.2 := by
  induction groups generalizing acc with
  | nil => exact prior
  | cons group rest ih =>
      have step := failureStep_sourceRecord errors acc group (key := key)
      apply ih (fusedFailureGroupStep errors acc group)
      rcases prior with represented | requested
      · exact step.2 represented
      · exact .inr (step.1 requested)

/-- Direct task failure retains each old source record or emits its source cleanup effect.
This proof permits the held computation's own rejection slot to change during settlement.
-/
theorem State.taskFailure_sourceRecord (state : State) (failed : Occurrence)
    (errors : Nat) {key} (represented : RecordTargetRepresented state.queue (.stream key))
    : RecordTargetRepresented (state.taskFailure failed errors).1.queue (.stream key)
      ∨ .cancelSource key
        ∈ (state.taskFailure failed errors).2.2.flatMap CleanupTarget.effects := by
  cases selected : state.queue.taskNode? failed with
  | none => simpa only [State.taskFailure, selected] using Or.inl represented
  | some input =>
      have stored := sourceRecord_putTaskRejection selected errors represented
      have progress := sourceRecord_failureFold errors input.task.groups
        (({ state with queue := state.queue.putTaskNode { input with rejection := some errors } }
          : State), [], []) (.inl stored)
      simp only [State.taskFailure, selected]
      rcases progress with retained | requested
      · exact .inl retained
      · exact .inr (List.mem_flatMap.mpr ⟨.stream key, requested, List.mem_cons_self⟩)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
