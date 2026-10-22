import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Initial activation metadata and its asynchronous specialization. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (NodeRefs)

/-- Synchronous startup preserves the exact original initial-announcement list. -/
theorem State.initializeWithStartup_initialGroups (work : Work) (startup : InitialStartup)
    : (State.initialize work startup).initialGroups
      = (State.initialize work).initialGroups :=
  rfl

/-- Startup never changes the initial stream notices. -/
theorem State.initializeWithStartup_initialStreams (work : Work)
    (startup : InitialStartup)
    : (State.initialize work startup).initialStreams
      = (State.initialize work).initialStreams :=
  rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

namespace GraphQL.IncrementalDelivery.EventSource
open ReferenceWorkQueue

/-- Empty startup adds no obligations to the ordinary event and start laws. -/
theorem ValidFor.of_asynchronous {work : Execution.Work}
    {source : EventSource (List GraphEvent)}
    (valid
      : source.history = []
        ∧ source.admissible []
        ∧ (∀ before after,
            before.IsPrefix after → source.admissible after → source.admissible before)
        ∧ ∀ inputs,
            source.admissible inputs
            → ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true)
    : source.ValidFor work := by
  refine ⟨by simp [InitialStartup.MatchesWork], valid.1, valid.2.1, valid.2.2.1, ?_⟩
  intro inputs admitted
  have checked := valid.2.2.2 inputs admitted
  refine ⟨checked.1, checked.2, ?_⟩
  cases inputs with
  | nil => trivial
  | cons first rest => intro failure impossible; cases impossible

end GraphQL.IncrementalDelivery.EventSource
