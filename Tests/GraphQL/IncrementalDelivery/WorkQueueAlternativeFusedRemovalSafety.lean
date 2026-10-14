import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalSafety

/-! Exact actual-walk safety target and trusted-axiom audit. No generated-state,
native acquisition, desired endpoint, or reference-equality premise is supplied here.
-/

namespace AlternativeFusedRemovalSafetyChecks
open GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

example : FusedRemovalSafety := FusedRemovalSafety_holds

example (state : State) (root : Nat) (targets : List CleanupTarget)
    {occurrence node key}
    (found : state.queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    : (state.removeGroup root targets).1.queue.taskNode? occurrence = some node
      ∨ .stream key ∈ (state.removeGroup root targets).2 :=
  (FusedRemovalSafety_holds state root targets).2.2 occurrence node key found held

#print axioms FusedRemovalSafety_holds
#print axioms removeGroup_walk_safety

end AlternativeFusedRemovalSafetyChecks
