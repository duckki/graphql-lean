import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence
import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! A later failure must not invalidate an earlier carrier's child announcement. -/

namespace GraphQL.IncrementalDelivery.Tests.FailureCutBoundary
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def stream : DeliveryNode := { ref := 0, path := [] }
private def child : DeliveryNode := { ref := 1, path := [.index 0] }
private def childTask : Occurrence := .executionGroup [0]

private def work : Work :=
  .stream stream
    [(
      .ok (.object [], 0),
      .executionGroup [{ node := child }] child.path (.error 1) .empty
    )]

private def matching : PublicationMatching := fun _ => .item [] 0

private def carrier : WorkQueueEvent :=
  .streamValues stream [{ item := .object [] }] [child] []

private theorem child_known
    : TaskAt work childTask [child.ref] (some (.item [] 0))
        (.object child.path (.error 1)) :=
  ⟨[{ node := child }], child.path, .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem child_node : NodeAt work child .group [] (some (.item [] 0)) :=
  ⟨
    [0],
    [{ node := child }],
    child.path,
    .error 1,
    .empty,
    [],
    { node := child },
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

/-- The stream item can initially publish and announce its child defer.
Witness: the child producer is this carrier, and no failure has yet occurred.
-/
theorem carrier_allowed : EventAllowed work [stream.ref] matching [] [] carrier := by
  refine ⟨[stream.ref], none, { item := .object [] }, rfl, .item .root rfl, ?_, ?_, ?_⟩
  · simp [CanPublish, Published, TaskCancelled, matching]
  · have opened : OpenOwner work [stream.ref] [] [stream.ref] stream :=
      ⟨⟨.stream, [], none, .stream .root⟩, by simp,
        by simp [Open, announcedRefs, completedRefs, pendingRefs]⟩
    refine ⟨opened, ⟨stream, opened, by simp [NodeFailed]⟩, ?_⟩
    intro other available
    have same : other.ref = stream.ref := List.mem_singleton.mp available.2.1
    obtain ⟨kind, deps, producer, known⟩ := available.1
    cases kind with
    | group =>
        obtain ⟨address, groups, path, result, children, enclosing, group,
          located, member, nodeEq, depsEq⟩ := known
        rcases address with _ | ⟨_ | index, _ | ⟨_ | edge, _ | ⟨next, rest⟩⟩⟩ <;>
          simp [Located, work, locateWork, locateWork.go, WorkLocation.child?] at located
        obtain ⟨⟨rfl, _, _, _⟩, _⟩ := located
        simp only [List.mem_singleton] at member
        subst group
        simp [nodeEq, child, stream] at same
    | stream =>
        obtain ⟨address, items, located⟩ := known
        rcases address with _ | ⟨_ | index, _ | ⟨_ | edge, _ | ⟨next, rest⟩⟩⟩ <;>
          simp [Located, work, locateWork, locateWork.go, WorkLocation.child?] at located
        simp [located.1.symm]
  · refine ⟨by decide, ?_, by simp⟩
    intro node member
    have same : node = child := by simpa using member
    subst node
    refine ⟨[], some (.item [] 0), child_node, ?_⟩
    refine ⟨by decide, Or.inl ⟨by simp [NodeFailed], Or.inr ?_⟩, ?_, by simp⟩
    · intro accounted
      rcases accounted childTask [child.ref] ⟨_, _, child_known⟩ (by simp) with
        cancelled | published
      · simp [TaskCancelled] at cancelled
      · obtain ⟨index, event, selected, _, same⟩ := published
        simp [matching, childTask] at same
    · intro source equal
      cases equal
      exact ⟨0, _, rfl, trivial, rfl⟩

/-- Initialization and the first carrier form an admitted atomic history.
Witness: the sole root stream is eligible, and the first carrier is permitted.
-/
theorem prefix_explained : Explains work [] [stream] [carrier] matching [] := by
  refine ⟨?_, by simp [FailureWitness], ?_⟩
  · refine ⟨⟨by decide, by simp, ?_⟩, by simp⟩
    intro node member
    have same : node = stream := by simpa using member
    subst node
    refine ⟨[], none, .stream .root, ?_⟩
    exact ⟨by decide, Or.inl ⟨by simp [NodeFailed], Or.inl rfl⟩, by simp, Or.inl rfl⟩
  · intro index event selected
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    have zero : index = 0 := by simp only [List.length_singleton] at bound; omega
    subst index
    have same : carrier = event := by simpa using selected
    subst event
    exact carrier_allowed

/-- The child's own failure is licensed immediately after its announcement.
Witness: its fixed failing outcome, structural reachability, and newly open ID.
-/
theorem failure_licensed
    : FailureWitness work [stream.ref] matching [carrier] [(1, childTask)] := by
  intro before cut occurrence after equal
  have sizes := congrArg List.length equal
  simp only [List.length_append, List.length_cons, List.length_nil] at sizes
  have emptyBefore : before = [] := List.eq_nil_of_length_eq_zero (by omega)
  have emptyAfter : after = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst before
  subst after
  have same : (1, childTask) = (cut, occurrence) := by simpa using equal
  cases same
  refine ⟨by decide, by simp, ?_, by simp [TaskCancelled]⟩
  refine ⟨
    [child.ref],
    some (.item [] 0),
    .object child.path (.error 1),
    child_known,
    rfl,
    ?_,
    child.ref,
    by simp,
    ?_
  ⟩
  · exact .child ⟨_, _, child_known⟩
      ⟨_, _, _, .item .root rfl, rfl⟩ (.root ⟨_, _, .item .root rfl⟩)
  · simp [announcedRefs, pendingRefs, eventPending, carrier, child, stream]

/-- Recording the child's later failure preserves the earlier child announcement.
Witness: output zero freezes its failure evidence before cut one.
-/
theorem later_failure_preserves_carrier
    : EventAllowed work [stream.ref] matching [] [(1, childTask)] carrier := by
  exact carrier_allowed

/-- The history remains explained after recording its newly announced child's failure.
Witness: unchanged initialization, the licensed cut, and preserved carrier admission.
-/
theorem later_failure_preserves_history
    : Explains work [] [stream] [carrier] matching [(1, childTask)] := by
  refine ⟨prefix_explained.1, failure_licensed, ?_⟩
  intro index event selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have zero : index = 0 := by simp only [List.length_singleton] at bound; omega
  subst index
  have same : carrier = event := by simpa using selected
  subst event
  exact later_failure_preserves_carrier

private def inputs : List (List ReferenceWorkQueue.GraphEvent) :=
  [
    [.streamItems stream
      [{
        occurrence := .item [] 0
        value := { item := .object [] }
        work := (ReferenceWorkQueue.streamItemWork? work (.item [] 0)).getD {}
      }]],
    [.taskFailure childTask 1],
    [.streamSuccess stream]
  ]

/-- The reference queue starts the child and accepts its immediately following failure.
Witness: executable reduction of the unchanged start/stop checker.
-/
example : ReferenceWorkQueue.inputsStarted work inputs = true := by native_decide

/-- The reference queue emits the announcement, then failure, then stream termination.
Witness: reduction of the normalized executable state machine, independently of admission.
-/
example
    : ((ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
        inputs).2
      = [
        [carrier],
        [.groupFailure child 1],
        [.streamSuccess stream, .workQueueTermination]
      ] := by
  cbv

end GraphQL.IncrementalDelivery.Tests.FailureCutBoundary
