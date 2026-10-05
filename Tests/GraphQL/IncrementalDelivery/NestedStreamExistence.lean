import Proofs.GraphQL.IncrementalDelivery.Correctness.NestedStreamExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization

/-! Complete nested-stream runs are constructed, not assumed as regression inputs. -/

namespace GraphQL.IncrementalDelivery.Tests.NestedStreamExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

/-- Four streams with distinct refs share a harmless fixed owner path in this raw fixture.
-/
def node (ref : NodeRef) : DeliveryNode := { ref, path := [] }

/-- Three publication levels and a sibling empty stream exercise dynamically introduced
notices, combine navigation, and cancellation of unpublished descendants after failures.
-/
def nested (outer middle inner : Result ResponseValue) : Work :=
  .stream (node 0)
    [(
      outer,
      .combine
        (.stream (node 1) [(middle, .stream (node 2) [(inner, .empty)])])
        (.stream (node 3) [])
    )]

/-- Positive failing outcomes admit a complete run through all fixture nesting levels.
Witness: the arbitrary-nesting existence theorem, without a supplied output history.
-/
theorem nested_run_exists (outer middle inner : Result ResponseValue)
    (outerPositive : BasicErrors.PositiveFailure outer)
    (middlePositive : BasicErrors.PositiveFailure middle)
    (innerPositive : BasicErrors.PositiveFailure inner)
    : ∃ history, AdmissibleRun (nested outer middle inner) history := by
  apply StreamOnly.completeRun_exists (paths := fun _ => []) (bound := 4)
  · simp [StreamOnly, nested]
  · simp [MixedOwnerPaths.WorkAt, OwnerPaths.Assigned, nested, node]
  · simp [ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder, nested, node]
  · simp [ExecutionErrors.WorkPositive, ExecutionErrors.ItemsPositive, nested,
      outerPositive, middlePositive, innerPositive]
  · simp [nested, Work.size]

/-- The child stream cannot be announced initially: its producer is still unpublished.
Witness: direct inversion of the producer-publication premise. The existence theorem
must therefore use a later notice-bearing event, not just initial-owner coverage.
-/
example (outer middle inner : Result ResponseValue)
    : ¬CanAnnounce (nested outer middle inner) [] (fun _ => .item [] 0) [] []
        (node 1) .stream [] (some (.item [] 0)) := by
  intro eligible
  have published := eligible.2.2.1 (.item [] 0) rfl
  simp [Published] at published

/-- Nested failure runs become complete observations through an actually conforming
queue constructor. Witness: terminal-run realization after constructive stream progress.
-/
example (response : Response)
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((nested (.ok (.null, 0)) (.error 1) (.ok (.null, 0))).size ≠ 0
          → (scheduler (nested (.ok (.null, 0)) (.error 1) (.ok (.null, 0)))).Conforms
              (nested (.ok (.null, 0)) (.error 1) (.ok (.null, 0))))
        ∧ (executionFromWork scheduler response
            (nested (.ok (.null, 0)) (.error 1) (.ok (.null, 0)))).Observes
            observed true := by
  apply (completeObservation_exists_iff _ _).mpr
  exact Or.inr
    (nested_run_exists _ _ _ (by simp [BasicErrors.PositiveFailure])
      (by simp [BasicErrors.PositiveFailure]) (by simp [BasicErrors.PositiveFailure]))

/-- An outer failure covers unannounced descendants at deeper response attachments.
Witness: positive counts, coherent refs, and the structural attachment-prefix certificate;
the existence proof constructs the report rather than assuming a terminal history.
-/
example
    : ∃ history,
        AdmissibleRun
          (.stream { ref := 0, path := [.field "rows"] }
            [(
              .error 1,
              .stream { ref := 1, path := [.field "rows", .index 0, .field "items"] }
                [(.ok (.null, 0), .empty)]
            )]) history := by
  apply StreamOnly.completeRun_exists
    (paths := fun ref => if ref = 0 then [.field "rows"]
      else [.field "rows", .index 0, .field "items"]) (bound := 2)
  · simp [StreamOnly]
  · simp [MixedOwnerPaths.WorkAt, OwnerPaths.Assigned]
  · simp [ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder]
  · simp [ExecutionErrors.WorkPositive, ExecutionErrors.ItemsPositive,
      BasicErrors.PositiveFailure]
  · decide

/-- A raw child at an unrelated attachment does not satisfy generated-work locality.
Witness: the parent's left scope is not a prefix of its child's right attachment.
-/
example
    : ¬ExecutionPaths.WorkUnder []
        (.stream { ref := 0, path := [.field "left"] }
          [(.error 1, .stream { ref := 1, path := [.field "right"] } [])]) := by
  simp [ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder]

/-- Notice coverage is not vacuous on control-only suffixes: reporting more failures
preserves it without announcing cancelled descendants. Witness: health monotonicity.
-/
example {work initial matching events failed more}
    (covered : DependencyFreeStreamsNotified work initial matching events failed)
    (included : failed ⊆ more) (stream : DeliveryNode) (errors : Nat)
    : DependencyFreeStreamsNotified work initial matching
        (events ++ [.streamFailure stream errors]) more :=
  covered.append_control (by simp [IsValue]) included

#print axioms StreamOnly.snapshot_cancelled_reported
#print axioms StreamOnly.cancelled_reported
#print axioms StreamOnly.completeRun_exists

end GraphQL.IncrementalDelivery.Tests.NestedStreamExistence
