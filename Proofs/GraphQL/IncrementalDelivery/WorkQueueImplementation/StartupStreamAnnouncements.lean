import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferenceAtoms

/-! Every actual startup stream reference has a strictly prior contributing notice. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Startup activates only streams already named in the original initial envelope. -/
theorem State.initializeWithStartup_streamRoots (input : Work) (startup : InitialStartup)
    : (State.initialize input startup).rootStreams.Subset
        ((State.initialize input startup).initialStreams.map
          Execution.DeliveryNode.ref) := by
  unfold State.initialize
  let integrated := ({} : State).maybeIntegrateWork input
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  have empty : pruned.1.rootStreams = [] := by
    rw [State.pruneEmptyGroups_rootStreams, State.maybeIntegrateWork_rootStreams]
  have included := pruned.1.startNewWork_rootStreams released startup.failures
  simpa only [State.enqueueGroupFailures, empty, List.nil_append] using included

/-- Actual FIFO replay retains prior notices for every stream reference. -/
theorem State.runNormalized_startup_streamReferencesAnnounced (queue : State)
    (batches : List (List GraphEvent))
    (initial : NodeRefs) (roots : queue.rootStreams.Subset initial)
    : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial
        (queue.runNormalized batches).2.flatten := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (roots : acc.1.rootStreams.Subset (initial ++ acc.2.2.flatten.flatMap streamNoticeRefs))
      (announced : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial
        acc.2.2.flatten)
      : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial
          (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc with
    | nil => exact announced
    | cons batch rest ih =>
        exact ih _ (normalizedStep_streamRoots acc batch roots)
          (normalizedStep_streamReferencesAnnounced acc batch roots announced)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have replay := loop batches (queue, publisher, [])
    (by simpa only [List.flatten_nil, List.flatMap_nil, List.append_nil] using roots) trivial
  exact replay

/-- Valid startup output retains initial or earlier stream notices at every atomic reference. -/
theorem State.startup_runNormalized_atomicStreamReferences {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      ReferencesAnnounced streamNoticeRefs streamReferenceRefs
        (initial.initialStreams.map Execution.DeliveryNode.ref)
        ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms) := by
  exact (State.runNormalized_startup_streamReferencesAnnounced _ _ _
    (State.initializeWithStartup_streamRoots _ startup)).publicationAtoms
    (State.runNormalized_nonemptyValues _ _ valid.nonemptyItems).2

/-- Every actual startup stream reference has a contributing announcement before its cut. -/
theorem State.startup_runNormalized_streamAnnouncedAt {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {index event ref}
    (atEvent
      : let initial := State.initialize (Work.fromExecution work) startup
        ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[index]?
        = some event)
    (reference : ref ∈ streamReferenceRefs event)
    : let initial := State.initialize (Work.fromExecution work) startup
      ref
      ∈ announcedRefs
          ((initial.initialGroups ++ initial.initialStreams).map
            Execution.DeliveryNode.ref)
          (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).take
            index) :=
  (State.startup_runNormalized_atomicStreamReferences startup valid).announcedRefs atEvent
    reference

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
