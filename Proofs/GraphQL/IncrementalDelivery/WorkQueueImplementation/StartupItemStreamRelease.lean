import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedItemStreamRelease

/-! Startup item-carrier notices retain their exact producers on the same inclusive item prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Source-valid startup derives item-stream release without extra output assumptions. -/
theorem State.startup_runNormalized_itemStreamReleasePublications {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      NormalizedItemStreamReleasePublications work
        (batches.flatten.flatMap GraphEvent.itemPublications)
        (initial.runNormalized batches).2.flatten :=
  State.runNormalized_itemStreamReleasePublications _ valid
    (by rwa [← inputsStartedWithStartup_eq_batchesStarted])

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
