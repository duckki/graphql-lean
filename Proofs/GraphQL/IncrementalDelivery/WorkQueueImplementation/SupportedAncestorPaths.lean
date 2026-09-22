import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay

/-! Actual generated replay connects healthy descendants to their live supporting ancestors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every live task-bearing ancestor reaches its healthy live descendant in actual replay.
Witness: generated parent chains, replay-derived complete links and registration, and the
accepted-failure retirement certificate. The path is concrete queue reachability, not an
additional source assumption; taskless intermediate registration records are included.
-/
theorem ExecutedWork.runNormalized_healthy_ancestor_path {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := (initial.runNormalized batches).1
      ∀ child dependencies ancestor occurrence owners,
        queue.groupNode? child.group.node.key = some child
        → GroupRecordAt work child.group.node dependencies
        → ¬GroupRecordInvalidated work
            (initial.objectFailureContributions batches.flatten) child.group.node.key
        → ancestor ∈ dependencies
        → TaskHasOwners work occurrence owners
        → ancestor ∈ owners
        → (∃ node, queue.groupNode? ancestor = some node)
        → queue.LiveDescendant ancestor child.group.node.key := by
  intro initial queue child dependencies ancestor occurrence owners
    found known healthy ancestorMember task contributes live
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work
  have closed := (createWorkQueue_parentRegistryClosed canonical).runNormalized
    registered.1 registered.2 batches
    (fun _ batch _ event => valid.eachMatches (List.mem_flatten.mpr ⟨_, batch, event⟩)) canonical
  exact (createWorkQueue_runNormalized_parentLinksComplete canonical valid).healthy_ancestor_path
    generated valid.runNormalized_groupNodesMatchWork
    (generated.runNormalized_healthyRetiredAncestors batches valid started)
    (createWorkQueue_runNormalized_registration valid).1 closed canonical found known healthy
    ancestorMember task contributes live

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
