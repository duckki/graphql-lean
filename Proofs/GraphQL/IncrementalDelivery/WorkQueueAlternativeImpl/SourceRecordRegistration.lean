import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceCacheRecords
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshotProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRootFrames

/-! Concrete source records survive registration before any group starts or disposes work.
Parent attachment may append child refs; the old stored-source evidence remains available.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- Attaching fresh streams retains an old source's active or buffered record. -/
theorem sourceRecord_addStreams (queue : ReferenceWorkQueue.State)
    (streams : List ReferenceWorkQueue.Stream) (producer : Option Occurrence) {key}
    (represented : RecordTargetRepresented queue (.stream key))
    : RecordTargetRepresented (queue.addStreams streams producer).1 (.stream key) := by
  cases represented with
  | activeStream active =>
      have roots : (queue.addStreams streams producer).1.rootStreams = queue.rootStreams := by
        unfold ReferenceWorkQueue.State.addStreams
        split
        · rfl
        · dsimp only
          split <;> rfl
      exact .activeStream (roots.symm ▸ active)
  | @bufferedStream occurrence node _ found stored held =>
      cases producer with
      | none => exact .bufferedStream found stored held
      | some parent =>
          unfold ReferenceWorkQueue.State.addStreams
          dsimp only
          split
          · exact .bufferedStream found stored held
          · rename_i parentNode selected
            by_cases same : parent = occurrence
            · subst parent
              have identical : parentNode = node := Option.some.inj (selected.symm.trans found)
              subst parentNode
              apply RecordTargetRepresented.bufferedStream (occurrence := occurrence)
              · exact ReferenceWorkQueue.State.putTaskNode_lookup_same found _
                  (ReferenceWorkQueue.State.taskNode?_some found).2
              · exact stored
              · exact List.mem_append_left _ held
            · refine RecordTargetRepresented.bufferedStream (occurrence := occurrence)
                (node := node) ?_ stored held
              exact ReferenceWorkQueue.State.putTaskNode_lookup_other found _ (by
                intro conflict
                exact same ((ReferenceWorkQueue.State.taskNode?_some selected).2.symm.trans
                  conflict))

/-- Delayed task registration changes neither source roots nor stored source attachments. -/
theorem State.addTask_sourceRecord (state : State) (task : ReferenceWorkQueue.Task) {key}
    (represented : RecordTargetRepresented state.queue (.stream key))
    : RecordTargetRepresented (state.addTask task).1.queue (.stream key) := by
  cases represented with
  | activeStream active =>
      have roots := congrArg ReferenceWorkQueue.State.rootStreams
        (state.addTask_registrationCore task)
      change (state.addTask task).1.queue.rootStreams = (state.queue.addTask task).rootStreams
        at roots
      rw [ReferenceWorkQueue.State.addTask_rootStreams] at roots
      exact .activeStream (roots.symm ▸ active)
  | bufferedStream found stored held =>
      exact .bufferedStream
        (by
          simpa only [ReferenceWorkQueue.State.taskNode?, State.addTask_taskNodes]
            using found)
        stored held

/-- Whole-scope registration retains each prior source record before activation. -/
theorem State.maybeIntegrateWork_sourceRecord (state : State)
    (work : ReferenceWorkQueue.Work) (producer : Option Occurrence) {key}
    (represented : RecordTargetRepresented state.queue (.stream key))
    : RecordTargetRepresented (state.maybeIntegrateWork work producer).1.queue
        (.stream key) := by
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (prior : RecordTargetRepresented acc.1.queue (.stream key))
      : RecordTargetRepresented (tasks.foldl registerTaskStep acc).1.queue (.stream key) := by
    induction tasks generalizing acc with
    | nil => exact prior
    | cons task rest ih =>
        apply ih
        unfold registerTaskStep
        dsimp only
        split <;> exact State.addTask_sourceRecord acc.1 task prior
  have grouped : RecordTargetRepresented (state.queue.addGroups work.groups).1 (.stream key) := by
    cases represented with
    | activeStream active =>
        exact .activeStream
          (by rw [ReferenceWorkQueue.State.addGroups_rootStreams]; exact active)
    | bufferedStream found stored held =>
        exact .bufferedStream
          (by
            simpa only [ReferenceWorkQueue.State.taskNode?,
              ReferenceWorkQueue.State.addGroups_taskNodes]
              using found)
          stored held
  exact sourceRecord_addStreams _ work.streams producer (loop work.tasks _ grouped)

/-- Replacing the completed value preserves old source attachments, including the input
task's own prior buffered record. The stored-value condition remains positive after replacement.
-/
theorem sourceRecord_putTaskValue {queue : ReferenceWorkQueue.State} {incoming input}
    (foundInput : queue.taskNode? incoming = some input)
    (value : Execution.ExecutionGroupValue) {key}
    (represented : RecordTargetRepresented queue (.stream key))
    : RecordTargetRepresented (queue.putTaskNode { input with value := some value })
        (.stream key) := by
  cases represented with
  | activeStream active => exact .activeStream active
  | @bufferedStream occurrence node _ found stored held =>
      by_cases same : occurrence = incoming
      · subst occurrence
        have identical : node = input := Option.some.inj (found.symm.trans foundInput)
        subst node
        exact .bufferedStream
          (ReferenceWorkQueue.State.putTaskNode_lookup_same foundInput _
            (ReferenceWorkQueue.State.taskNode?_some foundInput).2) rfl held
      · exact .bufferedStream
          (ReferenceWorkQueue.State.putTaskNode_lookup_other found _ (by
            intro conflict
            exact same
              (conflict.symm.trans (ReferenceWorkQueue.State.taskNode?_some foundInput).2)))
          stored held

/-- Recording a rejection preserves old source values and attachments at that computation. -/
theorem sourceRecord_putTaskRejection {queue : ReferenceWorkQueue.State} {failed input}
    (foundInput : queue.taskNode? failed = some input) (errors : Nat) {key}
    (represented : RecordTargetRepresented queue (.stream key))
    : RecordTargetRepresented (queue.putTaskNode { input with rejection := some errors })
        (.stream key) := by
  cases represented with
  | activeStream active => exact .activeStream active
  | @bufferedStream occurrence node _ found stored held =>
      by_cases same : occurrence = failed
      · subst occurrence
        have identical : node = input := Option.some.inj (found.symm.trans foundInput)
        subst node
        exact .bufferedStream
          (ReferenceWorkQueue.State.putTaskNode_lookup_same foundInput _
            (ReferenceWorkQueue.State.taskNode?_some foundInput).2) stored held
      · exact .bufferedStream
          (ReferenceWorkQueue.State.putTaskNode_lookup_other found _ (by
            intro conflict
            exact same
              (conflict.symm.trans (ReferenceWorkQueue.State.taskNode?_some foundInput).2)))
          stored held

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
