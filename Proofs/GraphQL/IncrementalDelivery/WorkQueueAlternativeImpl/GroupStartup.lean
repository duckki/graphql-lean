import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! Exact alternative startup reporting through its actual fused removal transition. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

/-- Failed startup reports the entire cached sum once, returning exactly the state and
cleanup targets of fused removal, with no subsequent private-task activation.
-/
theorem State.startGroup_reportsAllCachedFailures (state : State)
    (available : List (Occurrence × Nat)) (ref : NodeRef)
    (group : ReferenceWorkQueue.GroupNode) (targets : List CleanupTarget)
    (found : (state.queue.cacheTaskFailures available).groupNode? ref = some group)
    (failed
      : (group.tasks.filterMap
          (fun task =>
            ((state.queue.cacheTaskFailures available).taskNode? task).bind
              (·.rejection)))
        ≠ [])
    : state.startGroup ref targets available
      = let cached := { state with queue := state.queue.cacheTaskFailures available }
        let (next, cleanup) := cached.removeGroup group.group.node.ref targets
        (
          next,
          cleanup,
          [⟨
            group.group.node,
            (group.tasks.filterMap
              (fun task => (cached.queue.taskNode? task).bind (·.rejection))).sum
          ⟩]
        ) := by
  have nonempty : List.isEmpty (group.tasks.filterMap
      (fun task => ((state.queue.cacheTaskFailures available).taskNode? task).bind
        (·.rejection))) = false := by
    cases errors
          : group.tasks.filterMap
              (fun task =>
                ((state.queue.cacheTaskFailures available).taskNode? task).bind
                  (·.rejection)) with
    | nil => exact (failed errors).elim
    | cons _ _ => rfl
  simp only [State.startGroup, found, nonempty, Bool.false_eq_true, ↓reduceIte,
    State.finishGroupFailure]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
