import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferDependencies
import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedExistence

/-! Defer-only progress specializes the general mixed-work theorem.
The existing shape and complete-run interfaces remain available to callers.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Defer-only work supplies the general theorem's role and coverage premises
-----------------------------------------------------------------------------------------

/-- Every located defer-only subtree admits the constant defer-role assignment.
Witness: structural descent; a stream boundary contradicts the original shape.
-/
private theorem DeferOnly.roles_at {work address current producer owners}
    (shape : DeferOnly work) (located : Located work address current producer owners)
    : RefRoles.WorkRoles (fun _ => false) current := by
  cases current with
  | empty => simp [RefRoles.WorkRoles]
  | combine left right =>
      rw [RefRoles.WorkRoles]
      exact ⟨shape.roles_at (.left located), shape.roles_at (.right located)⟩
  | executionGroup groups path result children =>
      rw [RefRoles.WorkRoles]
      exact ⟨by simp, shape.roles_at (.executionGroup located)⟩
  | stream node items =>
      have impossible := shape _ _ _ _ (NodeAt.stream located)
      cases impossible
termination_by sizeOf current

/-- Defer-only work has coherent roles without any additional metadata premise.
Witness: the constant defer assignment, including all ancestor placeholders.
-/
theorem DeferOnly.roles {work} (shape : DeferOnly work)
    : RefRoles.WorkRoles (fun _ => false) work :=
  shape.roles_at Located.root

/-- No healthy descriptor has an eligible fresh notice. Failed reporting opportunities
are deliberately outside this proof-only progress construction.
-/
def HealthyNoticesCovered (work : Work) (initial : NodeRefs)
    (matching : PublicationMatching) (events : List WorkQueueEvent) (failed : FailureCuts)
    : Prop :=
  ∀ node kind dependencies producer,
    NodeAt work node kind dependencies producer
    → ¬NodeFailed work matching events failed node.ref
    → ¬CanAnnounce work initial matching events failed node kind dependencies producer

/-- Supported coverage equals healthy notice coverage for defer-only work.
Witness: the extra stream-dependency support clause is vacuous for every descriptor.
-/
theorem DeferOnly.supportedNoticesCovered_iff
    {ancestry work initial matching events failed} (shape : DeferOnly work)
    : SupportedNoticesCovered ancestry work initial matching events failed
      ↔ HealthyNoticesCovered work initial matching events failed := by
  constructor
  · intro covered node kind parents producer known healthy eligible
    have group := shape _ _ _ _ known
    subst kind
    exact covered node .group parents producer known
      ⟨eligible, healthy, by intro impossible; cases impossible⟩
  · intro covered node kind parents producer known supported
    exact covered node kind parents producer known supported.2.1 supported.1

-----------------------------------------------------------------------------------------
-- Existing defer-only interfaces reuse mixed progress
-----------------------------------------------------------------------------------------

/-- A ready announced defer task extends a healthy-notice-covering history.
Witness: specialize mixed supported extension without an explicit role assignment.
-/
theorem DeferOnly.extend_ready_covered
    {ancestry refBound paths bound work groups streams events matching failures occurrence
      owners producer payload}
    (shape : DeferOnly work) (valid : Valid ancestry refBound)
    (refs : MixedRefs.WorkAt ancestry 0 refBound work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : HealthyNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failures occurrence producer)
    (announced
      : ∃ ref ∈ owners,
          ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
          ∧ ¬NodeFailed work matching events failures ref)
    : ∃ event next cuts,
        Explains work groups streams (events ++ [event]) next cuts
        ∧ HealthyNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) next
            (events ++ [event]) cuts := by
  obtain ⟨event, next, cuts, extended, retained⟩ :=
    extend_ready_supported valid refs shape.roles continuous ordered coherent explained
      (shape.supportedNoticesCovered_iff.mpr covered) known ready announced
  exact ⟨event, next, cuts, extended, shape.supportedNoticesCovered_iff.mp retained⟩

/-- Coherent defer-only work has a complete run with shared owners and nested producers.
Witness: general mixed progress with the constant defer-role assignment. All original
premises are retained; no successful outcome or initial notice coverage is assumed.
-/
theorem DeferOnly.completeRun_exists
    {parents bound paths pathBound work}
    (shape : DeferOnly work)
    (valid : Valid parents bound) (coherent : MixedRefs.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history :=
  mixed_completeRun_exists valid coherent shape.roles continuous ordered pathCoherent
    nonempty

end GraphQL.IncrementalDelivery.Correctness
