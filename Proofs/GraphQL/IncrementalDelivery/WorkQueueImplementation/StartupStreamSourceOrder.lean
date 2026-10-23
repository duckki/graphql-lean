import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamClosureOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionSource

/-! Ordinary FIFO replay preserves exact source stream order and completion payloads. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Actual startup streamActions remain an ordered source subsequence for any initial queue. -/
theorem State.runNormalized_startup_streamActions (queue : State)
    (batches : List (List GraphEvent))
    : ((queue.runNormalized batches).2.flatten.filterMap streamAction).Sublist
        (batches.flatten.filterMap GraphEvent.streamAction) := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      : ((more.foldl normalizedStep acc).2.2.flatten.filterMap streamAction).Sublist
          (acc.2.2.flatten.filterMap streamAction
            ++ more.flatten.filterMap GraphEvent.streamAction) := by
    induction more generalizing acc with
    | nil => simp
    | cons batch rest ih =>
        rw [List.foldl_cons]
        have later := ih (normalizedStep acc batch)
        rw [normalizedStep_streamActions] at later
        have included := ((List.Sublist.refl (acc.2.2.flatten.filterMap streamAction)).append
          (acc.1.handleGraphEvents_streamActions batch)).append
          (.refl (rest.flatten.filterMap GraphEvent.streamAction))
        simpa [List.flatten_cons, List.filterMap_append, List.append_assoc]
          using later.trans included
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have replay := loop batches (queue, publisher, [])
  exact replay

/-- Actual startup streamCompletions remain an ordered source subsequence for any initial queue. -/
theorem State.runNormalized_startup_streamCompletions (queue : State)
    (batches : List (List GraphEvent))
    : ((queue.runNormalized batches).2.flatten.filterMap streamCompletion).Sublist
        (batches.flatten.filterMap GraphEvent.streamCompletion) := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      : ((more.foldl normalizedStep acc).2.2.flatten.filterMap streamCompletion).Sublist
          (acc.2.2.flatten.filterMap streamCompletion
            ++ more.flatten.filterMap GraphEvent.streamCompletion) := by
    induction more generalizing acc with
    | nil => simp
    | cons batch rest ih =>
        rw [List.foldl_cons]
        have later := ih (normalizedStep acc batch)
        rw [normalizedStep_streamCompletions] at later
        have included := ((List.Sublist.refl (acc.2.2.flatten.filterMap streamCompletion)).append
          (acc.1.handleGraphEvents_streamCompletions batch)).append
          (.refl (rest.flatten.filterMap GraphEvent.streamCompletion))
        simpa [List.flatten_cons, List.filterMap_append, List.append_assoc]
          using later.trans included
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have replay := loop batches (queue, publisher, [])
  exact replay

/-- Atomic startup stream references never follow an earlier closure of the same stream. -/
theorem State.startup_runNormalized_atomicStreamActions_ordered {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).filterMap
        streamAction).Pairwise
        StreamAction.Before :=
  streamActions_ordered_publicationAtoms
    (valid.streamActions_ordered.sublist (State.runNormalized_startup_streamActions _ _))

/-- Every actual atomic startup stream completion retains its exact source payload. -/
theorem State.runNormalized_startup_streamCompletion_source (queue : State)
    (batches : List (List GraphEvent))
    {event completion}
    (emitted : event ∈ (queue.runNormalized batches).2.flatten.flatMap publicationAtoms)
    (selected : streamCompletion event = some completion)
    : completion ∈ batches.flatten := by
  obtain ⟨original, member, within⟩ := List.mem_flatMap.mp emitted
  have inAtoms := List.mem_filterMap.mpr ⟨event, within, selected⟩
  rw [publicationAtoms_streamCompletions] at inAtoms
  have originalSelected : streamCompletion original = some completion := by simpa using inAtoms
  have inSource := (queue.runNormalized_startup_streamCompletions batches).subset
    (List.mem_filterMap.mpr ⟨original, member, originalSelected⟩)
  obtain ⟨source, member, same⟩ := List.mem_filterMap.mp inSource
  cases source <;> simp_all [GraphEvent.streamCompletion]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
