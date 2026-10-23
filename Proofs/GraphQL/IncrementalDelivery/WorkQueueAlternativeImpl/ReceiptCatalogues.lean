import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ActivationCatalogues
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationStreamReplay

/-! Permanent task catalogues and rejection provenance through actual item preparation. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- The actual item step appends its task catalogue without requiring eager node equality. -/
theorem streamRegistrationStep_tasks (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (streamRegistrationStep acc item available).1.queue.tasks
      = acc.1.queue.tasks ++ item.work.tasks := by
  change (({ (acc.1.maybeIntegrateWork item.work).1 with queue :=
    ((acc.1.maybeIntegrateWork item.work).1.queue.pruneEmptyGroups
      (acc.1.maybeIntegrateWork item.work).2.newGroups).1 }).startNewWork _ _ _
        available).1.queue.tasks = _
  rw [(State.startNewWork_permanentCatalogues _ _ _ _ available).1,
    ReferenceWorkQueue.State.pruneEmptyGroups_tasks, State.maybeIntegrateWork_tasks]

/-- The actual item fold appends each immediate task chunk exactly once in receipt order. -/
theorem streamRegistrationFold_tasks (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (items.foldl (fun acc item => streamRegistrationStep acc item available)
        acc).1.queue.tasks
      = acc.1.queue.tasks ++ items.flatMap (fun item => item.work.tasks) := by
  induction items generalizing acc with
  | nil => simp
  | cons item rest ih =>
      rw [List.foldl_cons, ih, streamRegistrationStep_tasks _ _ available]
      simp only [List.flatMap_cons, List.append_assoc]

/-- Receipt preparation preserves occurrence-indexed rejection facts independently of links. -/
theorem streamRegistrationStep_taskRejections {acc : StreamRegistrationAcc} {property}
    (prior : acc.1.queue.TaskRejectionsSatisfy property)
    (item : ReferenceWorkQueue.StreamItem)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (streamRegistrationStep acc item available).1.queue.TaskRejectionsSatisfy
        property :=
  State.startNewWork_taskRejections
    ((State.maybeIntegrateWork_taskRejections prior item.work).pruneEmptyGroups _) _ _ _
    available licensed

/-- Every actual receipt prefix retains only prior or supplied rejection causes. -/
theorem streamRegistrationFold_taskRejections (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc) {property}
    (prior : acc.1.queue.TaskRejectionsSatisfy property)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (items.foldl (fun acc item => streamRegistrationStep acc item available)
        acc).1.queue.TaskRejectionsSatisfy
        property := by
  induction items generalizing acc with
  | nil => exact prior
  | cons item rest ih =>
      exact ih _ (streamRegistrationStep_taskRejections prior item available licensed)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
