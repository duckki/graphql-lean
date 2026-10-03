import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementIntegration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GuardHealthCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureWitness
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A stream failure precedes a deferred failure below a retired taskless ancestor. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerMixedGuardHealth
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def child : DeliveryNode := ⟨1, [], some (.string "C")⟩
private def stream : DeliveryNode := { ref := 2, path := [.field "strict"] }
private def childTask : Occurrence := .executionGroup [1, 0]
private def failedItem : Occurrence := .item [0, 0, 1] 0

private def selections : List Selection :=
  [
    field "strict" [] [.stream (.boolean true) none (.int 1)],
    defer [defer [field "required"] (some "C")] (some "P")
  ]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def inputs : List (List GraphEvent) :=
  [[.streamFailure stream 1], [.taskFailure childTask 1]]

private def initial : State := State.initialize (Work.fromExecution work)

private def atoms : List WorkQueueEvent :=
  (initial.runNormalized inputs).2.flatten.flatMap publicationAtoms

/-- The mixed fixture is generated directly by a query with taskless outer defer P.
Witness: the defining pure-execution equation; no raw scheduler work is substituted.
-/
theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- Initialization accounts for retirement when taskless P is pruned to announce C.
Witness: the general generated-work theorem follows actual pruning, even though the
released child's defer ancestry is nonempty.
-/
theorem initial_retirement
    : initial.RootAncestorsRetired work ∧ initial.HealthyRetiredAncestors work [] :=
  generated.initialRetirement

private theorem stream_located
    : Located work [0, 0, 1] (.stream stream [(.error 1, .empty)]) none [] := by cbv

private theorem child_known
    : TaskAt work childTask [child.ref] none (.object [] (.error 1)) :=
  .executionGroup (groups := [⟨child, [parent]⟩]) (children := .empty)
    (owners := []) (by cbv)

/-- The host failures have fixed payloads, distinct identities, and accepted starts.
Witness: exact item/task locations and the unchanged executable start checker.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have first : ValidGraphEvents work [.streamFailure stream 1] :=
    .append .nil ⟨_, _, _, _, stream_located, .empty, List.mem_cons_self⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, stream_located, (by intro source impossible; cases impossible), .empty, rfl⟩
  refine ⟨.append first ⟨_, _, _, child_known⟩ ?_ ?_, by cbv⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, child_known, by intro source impossible; cases impossible⟩

/-- The independent stream closes first, followed by C's failure and termination.
Witness: evaluate the actual normalized replay; taskless P emits no completion.
-/
theorem output
    : atoms
      = [.streamFailure stream 1, .groupFailure child 1, .workQueueTermination] := by
  cbv

/-- The single stream cut names its actual failed item at output position zero.
Witness: the replay equation and exact item location, without assuming failure licensing.
-/
theorem stream_cuts : StreamFailureCuts work atoms [(0, failedItem)] := by
  constructor
  · rw [output]
    rfl
  · intro entry member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨stream, 1, none, by rw [output]; rfl, .item stream_located rfl⟩

/-- All source prefixes preserve the missing-parent boundary in this mixed replay.
Witness: general prefix health follows from generated work and the unchanged source laws.
The preceding stream failure is deliberately not an object contribution.
-/
theorem prefix_missing_parent_health
    : ∀ received : List GraphEvent,
        received.IsPrefix inputs.flatten
        → (initial.replayGraphEvents received).MissingParentAncestorsHealthy work
            (initial.objectFailureContributions received) :=
  generated.prefix_missingParentHealth source_valid.1 source_valid.2

/-- The accepted C settlement remains cleanup-safe under the full mixed predecessor list.
Witness: the general mixed-cut theorem, with the actual stream cut and replay-derived
missing-parent boundary. It retains the stream failure instead of dropping it
from the stated conclusion; historical producer-cancellation safety is not assumed.
-/
theorem child_owner_safe_after_stream_failure
    : ∃ owners ref,
        TaskHasOwners work childTask owners
        ∧ ref ∈ owners
        ∧ ¬GroupRecordInvalidated work [failedItem] ref := by
  have split
      : let publisher : IncrementalPublisher :=
          { active := initial.initialGroups ++ initial.initialStreams }
        let objects := sourceObjectFailureCuts 0
          (initial.eligibleFailureBlocks (initial.sourceRunBlocks publisher inputs).2.2)
        mergeFailureCuts objects [(0, failedItem)] = [(0, failedItem)] ++ [(1, childTask)] := by
    cbv
  exact createWorkQueue_mixedFailureCuts_uninvalidatedObjectOwner generated source_valid.1
    source_valid.2 prefix_missing_parent_health stream_cuts child_known split

/-- C's failure and the preceding stream failure share one cancellation-safe witness.
Witness: the general mixed construction retains the actual nonempty inventory and
batching. It proves cancellation exclusion, not just cleanup health.
-/
theorem mixed_failure_certificates
    : ∃ w : ConformancePlan.Witness,
        w.events = [.streamFailure stream 1, .groupFailure child 1]
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ ConformancePlan.AnnouncedFailures work w
        ∧ ConformancePlan.UncancelledFailures work w
        ∧ w.failures ≠ [] := by
  obtain ⟨w, history, shape, announced, safe⟩ :=
    ConformancePlan.mixed_failureCertificates generated source_valid.1 source_valid.2
  have sameHistory : w.events = [.streamFailure stream 1, .groupFailure child 1] := by
    rw [history]
    cbv
  refine ⟨w, sameHistory, shape, announced, safe, ?_⟩
  intro empty
  have count := announced.1.2.2.2.2 0 stream 1 (by rw [sameHistory]; rfl)
  simp [empty, failedBefore, NodeErrors] at count

/-- Cleanup of the taskless parent is unaffected by adding an unrelated failed item.
Witness: role-aware restriction on P's genuine registration descriptor, not an invented
task owner. This exercises the ancestor-only case of the new accounting equivalence.
-/
theorem taskless_parent_cleanup_ignores_stream
    : GroupRecordInvalidated work [failedItem, childTask] parent.ref
      ↔ GroupRecordInvalidated work [childTask] parent.ref := by
  have record : GroupRecordAt work parent [] :=
    ⟨[1, 0], [⟨child, [parent]⟩], [], .error 1, .empty, none, [], ⟨child, [parent]⟩,
      [], by cbv, List.mem_cons_self, List.suffix_cons _ _, rfl⟩
  apply generated.groupRecordInvalidated_iff_objectFailures record
    (fun _ member => List.mem_cons_of_mem _ member)
  intro occurrence owners producer path result known member
  rcases List.mem_cons.mp member with same | retained
  · subst occurrence
    obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
    cases impossible
  · exact retained

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerMixedGuardHealth
