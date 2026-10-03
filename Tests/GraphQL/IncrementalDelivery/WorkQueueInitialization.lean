import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConstructorInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Constructor facts do not assume the initialization condition they will establish.
Raw pruning is also checked separately from the execution-generated domain.
-/

namespace GraphQL.IncrementalDelivery.Tests.WorkQueueInitialization
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Generated initial notice refs are distinct without assuming valid initialization.
Witness: group pruning, stream registration, and disjoint execution ref roles.
-/
example {work} (executed : ExecutedWork work)
    : (((State.initialize (Work.fromExecution work)).initialGroups
        ++ (State.initialize (Work.fromExecution work)).initialStreams).map
        DeliveryNode.ref).Nodup :=
  executed.initialNoticeRefs_unique

/-- Initial group descriptors need no producer publication.
Witness: immediate contributor support survives pruning and descriptor coherence.
-/
example {work} (executed : ExecutedWork work) {group}
    (member : group ∈ (State.initialize (Work.fromExecution work)).initialGroups)
    : ∃ dependencies, NodeAt work group .group dependencies none :=
  executed.initialGroups_nodeAt member

/-- Generated initial groups have no ancestor contributions hidden behind later producers.
Witness: the constructor's retirement certificates and empty settlement history.
-/
example {work group dependencies} (executed : ExecutedWork work)
    (noticed : group ∈ (State.initialize (Work.fromExecution work)).initialGroups)
    (known : NodeAt work group .group dependencies none)
    : ∀ ref ∈ dependencies,
        ∀ occurrence owners, TaskHasOwners work occurrence owners → ref ∉ owners :=
  executed.initialGroups_ancestors_taskless noticed known

/-- Initialization follows from nonempty executed work, without a supplied notice law.
Witness: actual notice uniqueness, group/stream eligibility, and nonempty frontier.
-/
example {work} (executed : ExecutedWork work) (nonempty : work.size ≠ 0)
    : Initializes work (State.initialize (Work.fromExecution work)).initialGroups
        (State.initialize (Work.fromExecution work)).initialStreams :=
  executed.initializes nonempty

/-- Public conformance now derives initialization instead of requiring it from callers.
Witness: the strengthened public theorem, with unchanged source and constructor semantics.
-/
example (work : Execution.Work) (schedule : EventSource (List GraphEvent))
    (executed : ExecutedWork work) (nonempty : work.size ≠ 0)
    (valid : schedule.ValidFor work)
    : (ReferenceWorkQueue.createWorkQueueForSchedule work schedule).Conforms work :=
  createWorkQueueForScheduleConforms_holds work schedule executed nonempty valid

private def parent : DeliveryNode := { ref := 0, path := [] }
private def child : DeliveryNode := { ref := 1, path := [] }
private def other : DeliveryNode := { ref := 2, path := [] }

/-- Empty streams still supply a nonempty, eligible initial frontier.
Witness: concrete registration keeps the stream, then its producer-free descriptor
supplies the announcement rule. No event-source premise is used.
-/
example
    : let work := Execution.Work.stream child []
      let queue := State.initialize (Work.fromExecution work)
      Initializes work queue.initialGroups queue.initialStreams := by
  intro work queue
  apply (initializes_iff_static_frontier work).mpr
  change ([child].map DeliveryNode.ref).Nodup ∧
    (∀ group ∈ ([] : List DeliveryNode), _) ∧ [child] ≠ []
  exact ⟨by simp, by simp, by simp⟩

/-- Stream registration removes duplicate raw descriptors before producing notices.
Witness: direct reduction; the generic uniqueness theorem covers arbitrary streams.
-/
example
    : ((State.initialize { streams := [⟨child⟩, ⟨child⟩] }).initialStreams)
      = [child] := by
  rfl

/-- Execution can legitimately prune an ancestor which never owns any task.
Witness: the concrete nested-defer query announces only its inner group.
-/
example
    : let work :=
        ((executeRootSelectionSetCore schema resolvers [] 8 "Query"
            (.object "Query" 0) [defer [defer [field "a"]]]).run
          0).1.work
      let queue := State.initialize (Work.fromExecution work)
      queue.initialGroups.map DeliveryNode.ref = [1] ∧ queue.initialStreams = [] := by
  cbv

private def rawHiddenAncestor : Execution.Work :=
  .combine
    (.executionGroup [{ node := child, ancestors := [parent] }] [] (.ok ([], 0)) .empty)
    (.executionGroup [{ node := other }] [] (.ok ([], 0))
      (.executionGroup [{ node := parent }] [] (.ok ([], 0)) .empty))

/-- Local emptiness alone permits raw pruning to announce the child.
Witness: reduce immediate lowering; the parent's task is hidden behind the other producer.
This is a raw-work fixture, not a claimed execution-generated counterexample.
-/
example
    : (State.initialize (Work.fromExecution rawHiddenAncestor)).initialGroups
      = [child, other] := by
  rfl

/-- That raw child's descriptor is not eligible: its ancestor owns a later task.
Witness: the static eligibility equivalence and the hidden contributor at address [1, 0].
The generated-work proof must therefore use global ancestry, not only current task counts.
-/
example
    : ¬CanAnnounce rawHiddenAncestor [] (fun _ => .executionGroup []) [] []
        child .group [parent.ref] none := by
  have known : NodeAt rawHiddenAncestor child .group [parent.ref] none :=
    .group (.left .root) List.mem_cons_self
  have hidden : TaskHasOwners rawHiddenAncestor (.executionGroup [1, 0]) [parent.ref] :=
    ⟨some (.executionGroup [1]), .object [] (.ok ([], 0)),
      .executionGroup (.executionGroup (.right .root))⟩
  intro eligible
  have absent := ((group_canAnnounce_initial_iff known).mp eligible).2
    parent.ref List.mem_cons_self (.executionGroup [1, 0]) [parent.ref] hidden
  exact absent List.mem_cons_self

end GraphQL.IncrementalDelivery.Tests.WorkQueueInitialization
