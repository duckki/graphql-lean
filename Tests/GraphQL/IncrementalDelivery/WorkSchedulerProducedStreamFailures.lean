import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalItemStreamFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedStreamNoticeCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! General failure licensing covers object-produced and item-produced failing streams. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerProducedStreamFailures
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A retired successful defer owner protects the stream it released
-----------------------------------------------------------------------------------------

namespace ObjectProduced

private def selections : List Selection :=
  [defer [field "strict" [] [.stream (.boolean true) none (.int 1)]]]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def group : DeliveryNode := { ref := 0, path := [] }
private def stream : DeliveryNode := { ref := 1, path := [.field "strict"] }
private def producer : Occurrence := .executionGroup [1, 0]

private def children : Execution.Work :=
  .combine (.combine (.combine .empty .empty) (.stream stream [(.error 1, .empty)]))
    .empty

private def value : ExecutionGroupValue :=
  { deliveryGroups := [group], path := [], data := [("strict", .list [.scalar "x"])] }

private def first : GraphEvent :=
  .taskSuccess producer { value, work := Work.fromExecution children [1, 0, 0] }

private def inputs : List (List GraphEvent) := [[first], [.streamFailure stream 1]]

/-- The object-produced failure fixture uses actual query-generated work.
Witness: the defining executor equation, with one deferred streamed non-null list.
-/
theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- The successful group releases its stream before the failing item settles.
Witness: exact task/stream locations, prior producer success, and executable start checks.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have parent : TaskAt work producer [group.ref] none (.object [] (.ok (value.data, 0))) :=
    .executionGroup (groups := [⟨group, []⟩]) (children := children) (owners := []) (by cbv)
  have located : Located work [1, 0, 0, 0, 1]
      (.stream stream [(.error 1, .empty)]) (some producer) [group.ref] := by cbv
  have prior : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, parent, by cbv, by cbv⟩
      (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, parent, by intro source impossible; cases impossible⟩
  refine ⟨.append prior ⟨_, _, _, _, located, .empty, List.mem_cons_self⟩ ?_ ?_, by cbv⟩
  · simp [first, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, located,
      (by intro source same; cases same; simp [first, GraphEvent.successes]), .empty, rfl⟩

/-- The generated child stream is attached before its producer can be flushed.
Witness: the general fresh-producer registration theorem, instantiated at the actual
initial queue; the prepared node retains both its value and the child's stream ref.
-/
theorem child_stream_attached
    : let queue := State.initialize (Work.fromExecution work)
      let node : TaskNode := { task := ⟨producer, [group]⟩ }
      ∃ next,
        ((queue.putTaskNode { node with value := some value }).maybeIntegrateWork
            (Work.fromExecution children [1, 0, 0]) (some producer)).1.taskNode?
            producer
          = some next
        ∧ next.task = node.task
        ∧ next.value = some value
        ∧ stream.ref ∈ next.childStreams := by
  have parent : TaskAt work producer [group.ref] none (.object [] (.ok (value.data, 0))) :=
    .executionGroup (groups := [⟨group, []⟩]) (children := children) (owners := []) (by cbv)
  apply ExecutedWork.taskSuccess_prepared_childStream generated
    (before := []) .nil (stream := ⟨stream⟩) (node := { task := ⟨producer, [group]⟩ })
    (result := { value, work := Work.fromExecution children [1, 0, 0] })
  · exact ⟨_, _, parent, by cbv, by cbv⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities]
  · cbv
  · cbv; exact List.mem_cons_self

/-- The canonical mixed construction licenses the item failure after its owner retires.
Witness: instantiate the general theorem; the actual history still contains the producer
publication, group closure/release, and failed stream closure, under one failure witness.
-/
theorem failure_licensed
    : ∃ w : ConformancePlan.Witness,
        w.events
          = [
            .groupValues group
              [{
                path := [],
                data := value.data,
                errors := 0,
                deliveryGroups := value.deliveryGroups
              }],
            .groupSuccess group [] [stream],
            .streamFailure stream 1
          ]
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures := by
  obtain ⟨w, history, shape, licensed⟩ :=
    ConformancePlan.mixed_failureWitness_exists generated source_valid.1 source_valid.2
  refine ⟨w, ?_, shape, licensed⟩
  rw [history]
  cbv

/-- The released stream's failed completion obeys full event admission on that witness.
Witness: the shared canonical construction licenses failures and admits their controls
without reopening the already retired successful defer owner.
-/
theorem failure_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events = (ConformancePlan.initialQueue work).nonterminalAtoms inputs
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures
        ∧ ConformancePlan.FailureAdmission work w := by
  obtain ⟨w, history, shape, announced, uncancelled, admitted⟩ :=
    ConformancePlan.failureAdmission_certificates generated source_valid.1 source_valid.2
  exact ⟨w, history, shape, ConformancePlan.failureWitness announced uncancelled, admitted⟩

/-- A released stream's later failure does not invalidate its successfully retired group.
Witness: durable successful-group health on the same canonical licensed mixed inventory,
not a separate empty failure list or a caller-supplied record-health premise.
-/
theorem retired_group_healthy_after_stream_failure
    : ∃ w : ConformancePlan.Witness,
        w.events = (ConformancePlan.initialQueue work).nonterminalAtoms inputs
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures
        ∧ ¬NodeFailed work w.matching w.events w.failures group.ref := by
  obtain ⟨w, history, shape, announced, uncancelled, _, _, _, healthy⟩ :=
    ConformancePlan.mixed_groupHealthCertificates generated source_valid.1 source_valid.2
  refine ⟨w, history, shape, ConformancePlan.failureWitness announced uncancelled, ?_⟩
  apply healthy 1 group [] [stream]
  rw [history]
  cbv

/-- The stream's later failure does not invalidate its earlier group-carried notice.
Witness: the same canonical licensed witness supplies producer publication and carrier
health; only the concrete singleton notice's freshness is checked by evaluation.
-/
theorem notice_carrier_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events = (ConformancePlan.initialQueue work).nonterminalAtoms inputs
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures
        ∧ EventAllowed work (ConformancePlan.initialRefs work) w.matching
            (w.events.take 1) w.failures (.groupSuccess group [] [stream]) := by
  obtain ⟨w, history, _, announced, uncancelled, _, _, _, healthy, _, ledger, _,
    support, producers, _⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated source_valid.1 source_valid.2
  have selected : w.events[1]? = some (.groupSuccess group [] [stream]) := by
    rw [history]; cbv
  obtain ⟨dependencies, parent, located, eligible⟩ :=
    ConformancePlan.groupStreamNotice_canAnnounce generated source_valid.1 history announced
      support healthy producers selected List.mem_cons_self
      (by rw [history]; cbv; exact (by simp : 1 ∉ ([0] : List Nat)))
  refine ⟨w, history, ConformancePlan.failureWitness announced uncancelled, ?_⟩
  apply (ConformancePlan.groupSuccessAllowed_iff_announcements generated source_valid.1
    source_valid.2 history healthy ledger selected).mpr
  refine ⟨by simp, by simp, ?_⟩
  intro node member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨dependencies, parent, located, eligible⟩

end ObjectProduced

-----------------------------------------------------------------------------------------
-- A published outer item survives its stream's failure and protects a failing child stream
-----------------------------------------------------------------------------------------

namespace ItemProduced

private def localSchema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [{ name := "users", outputType := .list (.nonNull (.named "User")) }]
          },
        .object
          {
            name := "User",
            fields :=
              [{ name := "strict", outputType := .list (.nonNull (.named "String")) }]
          }
      ]
  }

private def localResolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ name _ _ =>
        if name = "users" then
          some (.list [.object "User" 0, .null])
        else
          some (.list [.scalar "x", .null]),
    resolve_argumentsEquivalent := by intros; rfl
  }

private def selections : List Selection :=
  [field "users" [field "strict" [] [.stream (.boolean true) none (.int 1)]] [.stream]]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore localSchema localResolvers [] 30 "Query"
      (.object "Query" 0) selections).run
    0).1.work

private def outer : DeliveryNode := { ref := 0, path := [.field "users"] }

private def child : DeliveryNode :=
  { ref := 1, path := [.field "users", .index 0, .field "strict"] }

private def producer : Occurrence := .item [0, 0, 1] 0
private def value : ResponseValue := .object [("strict", .list [.scalar "x"])]

private def children : Execution.Work :=
  .combine
    (.combine
      (.combine (.combine .empty .empty) (.stream child [(.error 1, .empty)])) .empty)
    .empty

private def entries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (value, 0), children), (.error 1, .empty)]

private def first : GraphEvent :=
  .streamItems outer [⟨producer, ⟨value, 0⟩, Work.fromExecution children [0, 0, 1, 0]⟩]

private def inputs : List (List GraphEvent) :=
  [[first], [.streamFailure outer 1], [.streamFailure child 1]]

/-- Actual execution generates two nested streams with distinct failed-item positions.
Witness: the root execution equation; the outer successful item retains the child's work.
-/
theorem generated : ExecutedWork work :=
  ⟨Nat, localSchema, localResolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- Both failures obey the source laws after the child-producing item succeeds.
Witness: exact nested locations and cursor positions; the child remains started after the
outer stream closes. No cancellation or output-admission fact is supplied as a premise.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have root : Located work [0, 0, 1] (.stream outer entries) none [] := by cbv
  have nested : Located work [0, 0, 1, 0, 0, 0, 1]
      (.stream child [(.error 1, .empty)]) (some producer) [] := by cbv
  have prior : ValidGraphEvents work [first] := by
    refine .append .nil ?_ ?_ ?_
    · intro supplied member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_, _, .item root rfl, by cbv⟩
    · simp [first, GraphEvent.Fresh, GraphEvent.identities]
    · exact ⟨_, _, _, _, root, by simp, by simp,
        (by intro source impossible; cases impossible), rfl⟩
  have two : ValidGraphEvents work [first, .streamFailure outer 1] := by
    refine .append prior ⟨_, _, _, _, root, .empty,
      List.mem_cons_of_mem _ List.mem_cons_self⟩ ?_ ?_
    · simp [first, GraphEvent.Fresh, GraphEvent.identities]
    · exact ⟨_, _, _, _, root, (by intro source impossible; cases impossible), .empty, rfl⟩
  refine ⟨.append two ⟨_, _, _, _, nested, .empty, List.mem_cons_self⟩ ?_ ?_, by cbv⟩
  · simp [first, outer, child, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, nested,
      (by intro source same; cases same; simp [first, GraphEvent.successes]), .empty, rfl⟩

/-- The item-produced stream completes even though its outer stream has failed first.
Witness: general complete notice coverage and actual terminal stream tracking, using the
canonical mixed history; no child notice or completed-ref premise is supplied.
-/
theorem child_completed_after_outer_failure
    : ∃ w : ConformancePlan.Witness,
        w.events = (ConformancePlan.initialQueue work).nonterminalAtoms inputs
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ child.ref ∈ completedRefs w.events := by
  obtain ⟨w, history, shape, _⟩ :=
    ConformancePlan.mixed_failureWitness_exists generated source_valid.1 source_valid.2
  refine ⟨w, history, shape, ?_⟩
  apply ConformancePlan.terminal_itemProducedStream_completed generated source_valid.1
    source_valid.2 history (by cbv)
    (address := [0, 0, 1]) (index := 0) (dependencies := [])
  · exact ⟨[0, 0, 1, 0, 0, 0, 1], [(.error 1, .empty)], by cbv⟩
  · simp [inputs, first, GraphEvent.successes, producer]

/-- Both failures are licensed on one matching despite the earlier outer-stream failure.
Witness: the general mixed theorem retains the successful carrier and both failure cuts;
it derives the item boundary's safety rather than assuming the child remains uncancelled.
-/
theorem failures_licensed
    : ∃ w : ConformancePlan.Witness,
        w.events
          = [
            .streamValues outer [⟨value, 0⟩] [] [child],
            .streamFailure outer 1,
            .streamFailure child 1
          ]
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures := by
  obtain ⟨w, history, shape, licensed⟩ :=
    ConformancePlan.mixed_failureWitness_exists generated source_valid.1 source_valid.2
  refine ⟨w, ?_, shape, licensed⟩
  rw [history]
  cbv

/-- Both failed stream controls are admitted after the child-producing item publishes.
Witness: retain one matching and both cuts; the outer failure does not invalidate the
child's open reference or erase its separately counted failure.
-/
theorem failures_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events = (ConformancePlan.initialQueue work).nonterminalAtoms inputs
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures
        ∧ ConformancePlan.FailureAdmission work w := by
  obtain ⟨w, history, shape, announced, uncancelled, admitted⟩ :=
    ConformancePlan.failureAdmission_certificates generated source_valid.1 source_valid.2
  exact ⟨w, history, shape, ConformancePlan.failureWitness announced uncancelled, admitted⟩

/-- A same-item child notice is admitted before both the outer and child streams fail.
Witness: retained producer labels and frozen failure cuts justify the carrier on the
same witness that licenses both later failures; no empty failure inventory is substituted.
-/
theorem notice_carrier_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events = (ConformancePlan.initialQueue work).nonterminalAtoms inputs
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures
        ∧ EventAllowed work (ConformancePlan.initialRefs work) w.matching
            (w.events.take 0) w.failures
            (.streamValues outer [⟨value, 0⟩] [] [child]) := by
  obtain ⟨w, history, _, announced, uncancelled, _, _, ready, _, _, _, _,
    support, producers, _⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated source_valid.1 source_valid.2
  have selected : w.events[0]? = some (.streamValues outer [⟨value, 0⟩] [] [child]) := by
    rw [history]; cbv
  have notice := ConformancePlan.itemStreamNotice_canAnnounce_of_replay generated
    source_valid.1 source_valid.2 history announced support producers selected
    List.mem_cons_self
  obtain ⟨parent, located, eligible⟩ := notice
  refine ⟨w, history, ConformancePlan.failureWitness announced uncancelled, ?_⟩
  apply (ConformancePlan.streamValueAllowed_iff_announcements ready selected).mpr
  refine ⟨by simp, by simp, ?_⟩
  intro node member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨[], parent, located, eligible⟩

end ItemProduced
end GraphQL.IncrementalDelivery.Tests.WorkSchedulerProducedStreamFailures
