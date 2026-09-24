import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferDependencies
import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedExistence

/-! Defer-only progress specializes the general mixed-work theorem.
The existing shape and complete-run interfaces remain available to callers.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Defer-only work supplies the general theorem's role and coverage premises
-----------------------------------------------------------------------------------------

/-- Every located defer-only subtree admits the constant defer-role assignment.
Witness: structural descent; a stream boundary contradicts the original shape.
-/
private theorem DeferOnly.roles_at {work address current producer owners}
    (shape : DeferOnly work) (located : Located work address current producer owners)
    : KeyRoles.WorkRoles (fun _ => false) current := by
  cases current with
  | empty => simp [KeyRoles.WorkRoles]
  | combine left right =>
      rw [KeyRoles.WorkRoles]
      exact ⟨shape.roles_at (.left located), shape.roles_at (.right located)⟩
  | executionGroup groups path result children =>
      rw [KeyRoles.WorkRoles]
      exact ⟨by simp, shape.roles_at (.executionGroup located)⟩
  | stream node items =>
      have impossible := shape _ _ _ _ (NodeAt.stream located)
      cases impossible
termination_by sizeOf current

/-- Defer-only work has coherent roles without any additional metadata premise.
Witness: the constant defer assignment, including all ancestor placeholders.
-/
theorem DeferOnly.roles {work} (shape : DeferOnly work)
    : KeyRoles.WorkRoles (fun _ => false) work :=
  shape.roles_at Located.root

/-- Supported coverage equals ordinary notice coverage when every descriptor is a group.
Witness: the stronger stream-dependency support clause is vacuous for defer-only work.
-/
theorem DeferOnly.supportedNoticesCovered_iff
    {ancestry work initial matching events failed} (shape : DeferOnly work)
    : SupportedNoticesCovered ancestry work initial matching events failed
      ↔ NoticesCovered work initial matching events failed := by
  refine ⟨?_, supportedNoticesCovered_of_noticesCovered⟩
  intro covered node kind parents producer known eligible
  have group := shape _ _ _ _ known
  subst kind
  exact covered node .group parents producer known
    ⟨eligible, by intro impossible; cases impossible⟩

-----------------------------------------------------------------------------------------
-- Existing defer-only interfaces reuse mixed progress
-----------------------------------------------------------------------------------------

/-- A ready announced defer task extends a notice-covering history.
Witness: specialize mixed supported extension and identify the two coverage predicates.
The original interface needs no explicit role assignment.
-/
theorem DeferOnly.extend_ready_covered
    {ancestry keyBound paths bound work groups streams events matching failures occurrence
      owners producer payload}
    (shape : DeferOnly work) (valid : Valid ancestry keyBound)
    (keys : MixedKeys.WorkAt ancestry 0 keyBound work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : NoticesCovered work ((groups ++ streams).map DeliveryNode.key) matching
          events (failures.map Prod.snd))
    (known : TaskAt work occurrence owners producer payload)
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    (announced
      : ∃ key ∈ owners,
          key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events
          ∧ ¬NodeFailed work (failedBefore failures events.length) key)
    : ∃ event next cuts,
        Explains work groups streams (events ++ [event]) next cuts
        ∧ NoticesCovered work ((groups ++ streams).map DeliveryNode.key) next
            (events ++ [event]) (cuts.map Prod.snd) := by
  obtain ⟨event, next, cuts, extended, retained⟩ :=
    extend_ready_supported valid keys shape.roles continuous ordered coherent explained
      (shape.supportedNoticesCovered_iff.mpr covered) known ready announced
  exact ⟨event, next, cuts, extended, shape.supportedNoticesCovered_iff.mp retained⟩

/-- Coherent defer-only work has a complete run with shared owners and nested producers.
Witness: general mixed progress with the constant defer-role assignment. All original
premises are retained; no successful outcome or initial notice coverage is assumed.
-/
theorem DeferOnly.completeRun_exists
    {parents bound paths pathBound work}
    (shape : DeferOnly work)
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history :=
  mixed_completeRun_exists valid coherent shape.roles continuous ordered pathCoherent
    nonempty

end GraphQL.IncrementalDelivery.Correctness
