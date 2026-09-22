import Proofs.GraphQL.IncrementalDelivery.Correctness.SingletonDeferExistence

/-! The producer-free singleton-defer progress theorem specializes nested-defer progress.
Its original shape and complete-run interface remain available to existing callers.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Producer-free specialization of singleton defer progress
-----------------------------------------------------------------------------------------

/-- All work nodes are producer-free defer groups, and every task has exactly one owner.
Several tasks may share a key; its coherent ancestor dependencies may be nonempty.
-/
def RootSingletonGroups (work : Work) : Prop :=
  (∀ node kind dependencies producer,
    NodeAt work node kind dependencies producer → kind = .group ∧ producer = none)
  ∧ ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload → ∃ key, owners = [key]

/-- Root singleton groups are singleton defer work with an additional shape restriction.
Witness: forget the producer-free requirement, retaining group kind and singleton owners.
-/
theorem RootSingletonGroups.toSingletonDefer {work} (shape : RootSingletonGroups work)
    : SingletonDefer work :=
  ⟨fun _ _ _ _ known => (shape.1 _ _ _ _ known).1, shape.2⟩

/-- Coherent root singleton defer work has a complete run even when ancestor dependencies
prevent initial coverage of all IDs. Witness: specialize the general singleton-defer
theorem to producer-free work. Outcomes and repeated tasks per key are
unrestricted; shared owner lists and nested producers are excluded by the shape premise.
-/
theorem RootSingletonGroups.completeRun_exists
    {parents bound paths pathBound work}
    (shape : RootSingletonGroups work)
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history :=
  shape.toSingletonDefer.completeRun_exists valid coherent continuous ordered
    pathCoherent nonempty

end GraphQL.IncrementalDelivery.Correctness
