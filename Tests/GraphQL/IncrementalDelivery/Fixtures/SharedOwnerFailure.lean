import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceOwnership
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents

/-! Generated shared-owner failure fixture with a held source below an object task.
The execution/source/start witnesses are kept separate from host resource acquisition.
-/

namespace GraphQL.IncrementalDelivery.Tests.SharedOwnerFailure
open AlternativeWorkQueue AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

def schema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [
                { name := "box", outputType := .named "Box" },
                { name := "badG", outputType := .nonNull (.named "String") },
                { name := "badH", outputType := .nonNull (.named "String") }
              ]
          },
        .object
          {
            name := "Box",
            fields :=
              [
                { name := "values", outputType := .list (.named "String") },
                { name := "dummy", outputType := .named "String" }
              ]
          }
      ]
  }

def resolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ field _ _ =>
        match field with
        | "box" => some (.object "Box" 1)
        | "values" => some (.list [])
        | "dummy" => some (.scalar "ok")
        | _ => none,
    resolve_argumentsEquivalent := by intros; rfl
  }

private def values : Selection := .field "values" "values" [] [.stream] []
private def badG : Selection := .field "badG" "badG" [] [] []
private def badH : Selection := .field "badH" "badH" [] [] []
private def boxG : Selection := .field "box" "box" [] [] [values]
private def boxH : Selection := .field "box" "box" [] [] [.field "dummy" "dummy" [] [] []]

def selections : List Selection :=
  [
    .inlineFragment none [.defer (.boolean true) (some (.string "G"))] [boxG, badG],
    .inlineFragment none [.defer (.boolean true) (some (.string "H"))] [boxH, badH]
  ]

def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 20 "Query" (.object "Query" 0)
      selections).run
    0).1.work

def groupG : DeliveryNode := { ref := 0, path := [], label := some (.string "G") }
def groupH : DeliveryNode := { ref := 1, path := [], label := some (.string "H") }
def source : DeliveryNode := { ref := 2, path := [.field "box", .field "values"] }

def streamWork : Execution.Work := .combine (.combine .empty (.stream source [])) .empty

def childWork : Execution.Work :=
  .combine
    (.combine .empty
      (.combine
        (.executionGroup [{ node := groupG }] [.field "box"]
          (.ok ([("values", .list [])], 0)) streamWork)
        (.combine
          (.executionGroup [{ node := groupH }] [.field "box"]
            (.ok ([("dummy", .scalar "ok")], 0)) (.combine .empty .empty))
          .empty)))
    .empty

def data : List (Name × ResponseValue) :=
  [("box", .object [])]

theorem work_shape
    : work
      = .combine .empty
          (.combine
            (.executionGroup [{ node := groupG }, { node := groupH }] []
              (.ok (data, 0)) childWork)
            (.combine (.executionGroup [{ node := groupG }] [] (.error 1) .empty)
              (.combine (.executionGroup [{ node := groupH }] [] (.error 1) .empty)
                .empty))) := by
  cbv

theorem executed : ReferenceWorkQueue.ExecutedWork work := by
  exact ⟨Nat, schema, resolvers, [], 20, "Query", .object "Query" 0, selections, rfl⟩

theorem nonempty : work.size ≠ 0 := by rw [work_shape]; decide

def parentSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [1, 0])
    {
      value := { deliveryGroups := [groupG, groupH], path := [], data }
      work := ReferenceWorkQueue.Work.fromExecution childWork [1, 0, 0]
    }

def heldProducer : Occurrence := .executionGroup [1, 0, 0, 0, 1, 0]

def success : GraphEvent :=
  .taskSuccess heldProducer
    {
      value :=
        {
          deliveryGroups := [groupG],
          path := [.field "box"],
          data := [("values", .list [])]
        }
      work := ReferenceWorkQueue.Work.fromExecution streamWork [1, 0, 0, 0, 1, 0, 0]
    }

def failureG : GraphEvent := .taskFailure (.executionGroup [1, 1, 0]) 1
def failureH : GraphEvent := .taskFailure (.executionGroup [1, 1, 1, 0]) 1

def inputs : List (List GraphEvent) :=
  [[parentSuccess], [success], [failureG], [failureH]]

private theorem shared_task
    : TaskAt work (.executionGroup [1, 0]) [0, 1] none (.object [] (.ok (data, 0))) := by
  refine ⟨[{ node := groupG }, { node := groupH }], [],
    .ok (data, 0), childWork, [], ?_, rfl, rfl⟩
  rw [work_shape]
  rfl

private theorem source_task
    : TaskAt work heldProducer [0] (some (.executionGroup [1, 0]))
        (.object [.field "box"] (.ok ([("values", .list [])], 0))) := by
  refine ⟨[{ node := groupG }], [.field "box"], .ok ([("values", .list [])], 0),
    streamWork, [0, 1], ?_, rfl, rfl⟩
  rw [work_shape]
  rfl

private theorem g_task
    : TaskAt work (.executionGroup [1, 1, 0]) [0] none (.object [] (.error 1)) := by
  refine ⟨[{ node := groupG }], [], .error 1, .empty, [], ?_, rfl, rfl⟩
  rw [work_shape]
  rfl

private theorem h_task
    : TaskAt work (.executionGroup [1, 1, 1, 0]) [1] none (.object [] (.error 1)) := by
  refine ⟨[{ node := groupH }], [], .error 1, .empty, [], ?_, rfl, rfl⟩
  rw [work_shape]
  rfl

theorem parent_success_matches : parentSuccess.MatchesWork work := by
  refine ⟨[0, 1], none, shared_task, ?_, ?_⟩
  all_goals rw [work_shape]; rfl

theorem success_matches : success.MatchesWork work := by
  refine ⟨[0], some (.executionGroup [1, 0]), source_task, ?_, ?_⟩
  all_goals rw [work_shape]; rfl

theorem failureG_matches : failureG.MatchesWork work := ⟨[0], none, [], g_task⟩
theorem failureH_matches : failureH.MatchesWork work := ⟨[1], none, [], h_task⟩

theorem valid_events : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten := by
  have first : ReferenceWorkQueue.ValidGraphEvents work [parentSuccess] :=
    .append .nil parent_success_matches (by simp [ReferenceWorkQueue.GraphEvent.Fresh,
      ReferenceWorkQueue.GraphEvent.identities, parentSuccess])
      ⟨[0, 1], none, _, shared_task, fun _ impossible => by cases impossible⟩
  have sourceReady : success.Ready work [parentSuccess] := by
    refine ⟨[0], some (.executionGroup [1, 0]), _, source_task, ?_⟩
    intro producer same
    cases same
    simp [ReferenceWorkQueue.GraphEvent.successes, parentSuccess]
  have second : ReferenceWorkQueue.ValidGraphEvents work [parentSuccess, success] :=
    .append first success_matches (by simp [ReferenceWorkQueue.GraphEvent.Fresh,
      ReferenceWorkQueue.GraphEvent.identities, parentSuccess, success, heldProducer]) sourceReady
  have third : ReferenceWorkQueue.ValidGraphEvents work [parentSuccess, success, failureG] :=
    .append second failureG_matches (by simp [ReferenceWorkQueue.GraphEvent.Fresh,
      ReferenceWorkQueue.GraphEvent.identities, parentSuccess, success, heldProducer, failureG])
      ⟨[0], none, _, g_task, fun _ impossible => by cases impossible⟩
  exact .append third failureH_matches
    (by
      simp [ReferenceWorkQueue.GraphEvent.Fresh,
        ReferenceWorkQueue.GraphEvent.identities, parentSuccess, success, heldProducer, failureG, failureH])
    ⟨[1], none, _, h_task, fun _ impossible => by cases impossible⟩

theorem started : ReferenceWorkQueue.inputsStarted work inputs = true := by
  rw [work_shape]
  cbv

def schedule : EventSource (List GraphEvent) := .ofList inputs

private theorem prefix_cases {batches : List (List GraphEvent)}
    (earlier : batches.IsPrefix inputs)
    : batches = []
      ∨ batches = [[parentSuccess]]
      ∨ batches = [[parentSuccess], [success]]
      ∨ batches = [[parentSuccess], [success], [failureG]]
      ∨ batches = inputs := by
  have bound : batches.length ≤ 4 := earlier.length_le
  have chosen := List.prefix_iff_eq_take.mp earlier
  have lengths : batches.length = 0 ∨ batches.length = 1 ∨ batches.length = 2
      ∨ batches.length = 3 ∨ batches.length = 4 := by omega
  rcases lengths with zero | one | two | three | four
  · left; simpa [zero] using chosen
  · right; left; simpa [one, inputs] using chosen
  · right; right; left; simpa [two, inputs] using chosen
  · right; right; right; left; simpa [three, inputs] using chosen
  · right; right; right; right; simpa [four, inputs] using chosen

theorem source_valid : schedule.ValidFor work := by
  refine ⟨rfl, List.nil_prefix, ?_, ?_⟩
  · intro before after earlier admitted
    exact earlier.trans admitted
  · intro batches admitted
    rcases prefix_cases admitted with rfl | rfl | rfl | rfl | rfl
    · exact ⟨.nil, rfl⟩
    · refine ⟨valid_events.prefix ?_, ?_⟩
      · exact ⟨[success, failureG, failureH], rfl⟩
      · rw [work_shape]; cbv
    · refine ⟨valid_events.prefix ?_, ?_⟩
      · exact ⟨[failureG, failureH], rfl⟩
      · rw [work_shape]; cbv
    · refine ⟨valid_events.prefix ?_, ?_⟩
      · exact ⟨[failureH], rfl⟩
      · rw [work_shape]; cbv
    · exact ⟨valid_events, started⟩

theorem admitted : schedule.admissible inputs := List.prefix_refl _

def staged : GraphBatchResult :=
  ((State.initialize work).handleGraphEvents [parentSuccess]).state.handleGraphEvents
    [success]

def firstFailure : GraphBatchResult := staged.state.handleGraphEvents [failureG]
def lastFailure : GraphBatchResult := firstFailure.state.handleGraphEvents [failureH]

def leases : ResourceState :=
  ResourceState.adopt
    (ResourceState.empty.set (.stream 2) (.owned (.producer heldProducer))) heldProducer
    [.stream 2]

theorem handoff
    : ResourceReplay ResourceState.empty
        [.acquire (.stream 2) (.producer heldProducer), .adopt heldProducer [.stream 2]]
        leases := by
  exact .cons (.acquire _ _ _ rfl) (.cons (.adopt _ _ _) (.nil _))

theorem adoption_observed : staged.effects = [.adopt heldProducer] := by
  cbv

theorem source_owned : leases (.stream 2) = .owned .queue := by
  simp [leases, ResourceState.adopt, ResourceState.set]

theorem staged_coverage : StopCoverage staged.state leases := by
  intro target owned
  by_cases same : target = .stream 2
  · subst target
    cbv
    exact .tail _ (.tail _ (.tail _ (.head _)))
  · simp [leases, ResourceState.adopt, ResourceState.set, ResourceState.empty, same] at owned

theorem failure_loses_reachability
    : (.stream 2 : CleanupTarget) ∉ lastFailure.state.cleanupTargets := by
  cbv
  exact List.not_mem_nil

theorem failure_effects
    : firstFailure.effects ++ lastFailure.effects
      = [
        .abortTask heldProducer,
        .cancelSource 2,
        .abortStreamQueue 2,
        .abortTask (.executionGroup [1, 0]),
        .abortTask (.executionGroup [1, 0, 0, 0, 1, 1, 0])
      ] := by cbv

def requested : ResourceState := leases.set (.stream 2) (.cleanupRequested .queue)

theorem disposal
    : .cancelSource 2 ∈ firstFailure.effects ++ lastFailure.effects
      ∧ ResourceReplay leases [.requestCleanup (.stream 2)] requested := by
  refine ⟨?_, .cons (.request _ _ .queue source_owned) (.nil _)⟩
  rw [failure_effects]
  exact .tail _ (.head _)

theorem final_coverage : StopCoverage lastFailure.state requested := by
  intro target owned
  by_cases same : target = .stream 2
  all_goals simp [requested, leases, ResourceState.adopt, ResourceState.set,
    ResourceState.empty, same] at owned

theorem terminated : lastFailure.state.queue.terminated = true := by cbv

theorem actual_replay_state
    : ((State.initialize work).runNormalized inputs).1 = lastFailure.state := by cbv

/-- The generated regression retains every query/source/start premise and observes
disposal before accounting retirement. Ghost cleanup requested is not native settlement.
-/
theorem generated_disposal
    : ReferenceWorkQueue.ExecutedWork work
      ∧ work.size ≠ 0
      ∧ schedule.ValidFor work
      ∧ schedule.admissible inputs
      ∧ ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
      ∧ ReferenceWorkQueue.inputsStarted work inputs = true
      ∧ ResourceReplay ResourceState.empty
          [.acquire (.stream 2) (.producer heldProducer), .adopt heldProducer [.stream 2]]
          leases
      ∧ leases (.stream 2) = .owned .queue
      ∧ staged.effects = [.adopt heldProducer]
      ∧ StopCoverage staged.state leases
      ∧ .cancelSource 2 ∈ firstFailure.effects ++ lastFailure.effects
      ∧ ResourceReplay leases [.requestCleanup (.stream 2)] requested
      ∧ StopCoverage lastFailure.state requested
      ∧ ((State.initialize work).runNormalized inputs).1 = lastFailure.state
      ∧ lastFailure.state.queue.terminated = true :=
  ⟨
    executed,
    nonempty,
    source_valid,
    admitted,
    valid_events,
    started,
    handoff,
    source_owned,
    adoption_observed,
    staged_coverage,
    disposal.1,
    disposal.2,
    final_coverage,
    actual_replay_state,
    terminated
  ⟩

end GraphQL.IncrementalDelivery.Tests.SharedOwnerFailure
