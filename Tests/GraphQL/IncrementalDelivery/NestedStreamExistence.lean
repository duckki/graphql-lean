import Proofs.GraphQL.IncrementalDelivery.Correctness.NestedStreamExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization

/-! Complete nested-stream runs are constructed, not assumed as regression inputs. -/

namespace GraphQL.IncrementalDelivery.Tests.NestedStreamExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

/-- Four differently keyed streams share a harmless fixed owner path in this raw fixture.
-/
def node (key : Nat) : DeliveryNode := { key, path := [] }

/-- Three publication levels and a sibling empty stream exercise dynamically introduced
notices, append navigation, and cancellation of unpublished descendants after failures.
-/
def nested (outer middle inner : Result ResponseValue) : Work :=
  .stream (node 0)
    [(
      outer,
      .append
        (.stream (node 1) [(middle, .stream (node 2) [(inner, .empty)])])
        (.stream (node 3) [])
    )]

/-- All fixture outcomes admit a complete run, including raw zero-count errors.
Witness: the arbitrary-nesting existence theorem, without a supplied output history.
-/
theorem nested_run_exists (outer middle inner : Result ResponseValue)
    : ∃ history, AdmissibleRun (nested outer middle inner) history := by
  apply StreamOnly.completeRun_exists (paths := fun _ => []) (bound := 4)
  · simp [StreamOnly, nested]
  · simp [MixedOwnerPaths.WorkAt, OwnerPaths.Assigned, nested, node]
  · simp [nested, Work.size]

/-- The child stream cannot be announced initially: its producer is still unpublished.
Witness: direct inversion of the producer-publication premise. The existence theorem
must therefore use a later notice-bearing event, not just initial-owner coverage.
-/
example (outer middle inner : Result ResponseValue)
    : ¬CanAnnounce (nested outer middle inner) [] (fun _ => .item [] 0) [] []
        (node 1) .stream [] (some (.item [] 0)) := by
  intro eligible
  have published := eligible.2.2.2.1 (.item [] 0) rfl
  simp [Published] at published

/-- Nested failure runs become complete observations through an actually conforming
factory. Witness: terminal-run realization after constructive stream progress.
-/
example (response : Response)
    : ∃ scheduler : Execution.WorkScheduler,
      ∃ observed : QueryResult,
        scheduler.Conforms (nested (.ok (.null, 0)) (.error 0) (.ok (.null, 0)))
        ∧ (executionFromWork scheduler response
            (nested (.ok (.null, 0)) (.error 0) (.ok (.null, 0)))).Observes
            observed true :=
  (completeObservation_exists_iff _ _).mpr (Or.inr (nested_run_exists _ _ _))

/-- Notice coverage is not vacuous on control-only suffixes: reporting more failures
preserves it without announcing cancelled descendants. Witness: health monotonicity.
-/
example {work initial matching events failed more}
    (covered : ParentlessStreamsNotified work initial matching events failed)
    (included : failed ⊆ more) (stream : DeliveryNode) (errors : Nat)
    : ParentlessStreamsNotified work initial matching
        (events ++ [.streamFailure stream errors]) more :=
  covered.append_control (by simp [IsValue]) included

end GraphQL.IncrementalDelivery.Tests.NestedStreamExistence
