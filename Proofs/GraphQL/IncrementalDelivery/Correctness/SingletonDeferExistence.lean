import Proofs.GraphQL.IncrementalDelivery.Correctness.SingletonDeferDependencies
import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferExistence

/-! Singleton-defer existence specializes the general shared-owner defer-only theorem. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

/-- Coherent singleton defer work has a complete run even when ancestor dependencies
prevent initial coverage of all IDs. Witness: specialize general defer-only progress
to singleton owner lists. Outcomes and repeated tasks per key are
unrestricted, including nested producers; streams and shared owner lists are excluded.
-/
theorem SingletonDefer.completeRun_exists
    {parents bound paths pathBound work}
    (shape : SingletonDefer work)
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history :=
  shape.toDeferOnly.completeRun_exists valid coherent continuous ordered pathCoherent
    nonempty

end GraphQL.IncrementalDelivery.Correctness
