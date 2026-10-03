import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootGroupCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingHealthy
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayCancellation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureOutput
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Minimality
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Cancelled settlements are ignored while their earlier failure notices are retained. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerCancelledFailure
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated shared contributors with a failed defer ancestor
-----------------------------------------------------------------------------------------

private def root : DeliveryNode := { ref := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { ref := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 2, path := [], label := some (.string "C") }
private def other : DeliveryNode := { ref := 3, path := [], label := some (.string "D") }
private def nested : DeliveryNode := { ref := 4, path := [], label := some (.string "E") }
private def firstTask : Occurrence := .executionGroup [1, 0]
private def secondTask : Occurrence := .executionGroup [1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def data : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩, ⟨other, [parent]⟩] [] (.error 1)
        .empty)
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩, ⟨nested, [other, parent]⟩]
          [] (.error 2) .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] (.ok (data, 0)) (.combine .empty .empty))
          .empty)))

private def first : GraphEvent := .taskFailure firstTask 1
private def second : GraphEvent := .taskFailure secondTask 2

private def finish : GraphEvent :=
  .taskSuccess parentTask
    {
      value := { deliveryGroups := [parent], path := [], data },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def inputs : List (List GraphEvent) := [[first], [second], [finish]]

/-- Execution generates two differently owned failing partitions sharing R and C.
Witness: the second task's other owner E is a child of the first task's owner D.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "first"), field "fail",
        field "required" [] [] (some "second")] (some "R"),
      defer [field "a",
        defer [field "required" [] [] (some "first"), field "fail",
          field "required" [] [] (some "second")] (some "C"),
        defer [field "required" [] [] (some "first"),
          defer [field "fail", field "required" [] [] (some "second")] (some "E")]
          (some "D")] (some "P")], ?_⟩
  cbv

/-- The host may still report the already-started task after its owners have failed.
Witness: the unchanged sequential start checker accepts the late settlement.
-/
theorem inputs_started : inputsStarted work inputs = true := by cbv

private theorem first_known
    : TaskAt work firstTask [root.ref, child.ref, other.ref] none
        (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem second_known
    : TaskAt work secondTask [root.ref, child.ref, nested.ref] none
        (.object [] (.error 2)) :=
  ⟨_, [], .error 2, .empty, [], rfl, rfl, rfl⟩

private theorem parent_known
    : TaskAt work parentTask [parent.ref] none (.object [] (.ok (data, 0))) :=
  ⟨_, [], .ok (data, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩

/-- Both failures and the later parent success satisfy the unchanged source semantics.
Witness: fixed outcomes, fresh occurrences, and root structural producers.
-/
theorem source_valid : ValidGraphEvents work inputs.flatten := by
  have one : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, _, first_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first])
      ⟨_, _, _, first_known, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [first, second] :=
    .append one ⟨_, _, _, second_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first, second,
        firstTask, secondTask])
      ⟨_, _, _, second_known, by intro source impossible; cases impossible⟩
  exact .append two ⟨_, _, parent_known, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, first, second, finish,
      firstTask, secondTask, parentTask])
    ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩

/-- Former incorrect output, retained as an independent contract counterexample. -/
private def outputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure root 1],
    [
      .groupValues parent
        [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
      .groupSuccess parent [child, other] [],
      .groupFailure child 3,
      .groupFailure other 1,
      .workQueueTermination
    ]
  ]

private def correctedOutputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure root 1],
    [
      .groupValues parent
        [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
      .groupSuccess parent [child, other] [],
      .groupFailure child 1,
      .groupFailure other 1,
      .workQueueTermination
    ]
  ]

/-- C and D retain only the first failure; the cancelled contributor adds no errors.
Witness: exact queue/publisher replay with normal notices before both delayed closures.
-/
theorem output
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
      = correctedOutputs := by
  cbv

/-- The same cancellation check applies between settlements inside one host batch.
Witness: reduction of the sequential batch handler, preserving all output atoms.
-/
theorem batched_output
    : ((State.initialize (Work.fromExecution work)).runNormalized
        [[first, second, finish]]).2
      = [correctedOutputs.flatten] := by
  cbv

/-- Direct failed owners and E's failed ancestor jointly invalidate the second task.
Witness: evaluate the healthy-owner guard after the first failure, before the late input.
-/
theorem second_has_noHealthyOwner
    : let queue := ((State.initialize (Work.fromExecution work)).handleGraphEvent first).1
      queue.taskHasHealthyOwner ⟨secondTask, [root, child, nested]⟩ = false := by
  cbv

/-- Both settlements retain safe counters, including the ignored second failure.
Witness: the general active-or-cancelled failure bound and the ignored-handler theorem,
applied to the actual generated queue rather than an assumed admissible output trace.
-/
theorem second_pendingBound
    : let queue := ((State.initialize (Work.fromExecution work)).handleGraphEvent first).1
      (queue.handleGraphEvent second).1.PendingBound (fun _ => True)
        [secondTask, firstTask] := by
  let initial := State.initialize (Work.fromExecution work)
  let taskNode : TaskNode := { task := ⟨firstTask, [root, child, other]⟩ }
  have found : initial.taskNode? firstTask = some taskNode := by
    dsimp only [initial, taskNode]
    cbv
  have owned : initial.OwnedExactlyBy firstTask [root.ref, child.ref, other.ref] := by
    intro node member
    dsimp only [initial] at member
    cbv at member
    rcases List.mem_cons.mp member with rfl | member
    · simp [firstTask, root, child, other]
    rcases List.mem_cons.mp member with rfl | member
    · simp [firstTask, root, child, other]
    rcases List.mem_cons.mp member with rfl | member
    · simp [firstTask, root, child, other]
    rcases List.mem_cons.mp member with rfl | member
    · simp [firstTask, root, child, other]
    obtain rfl := List.mem_singleton.mp member
    simp [firstTask, root, child, other]
  have prior := (createWorkQueue_pendingBound_empty (Work.fromExecution work)).taskFailure
    (createWorkQueue_groupRefsUnique _) (createWorkQueue_taskMembershipsUnique _)
    firstTask 1 taskNode found (by simp) (by decide) owned
  exact prior.taskFailure_of_noHealthyOwner
    (node := { task := ⟨secondTask, [root, child, nested]⟩ })
    (by cbv) second_has_noHealthyOwner 2

/-- General replay accounting covers the cancelled settlement without any output premise.
Witness: the generated-work replay theorem applied to the two-failure source prefix;
its ledger retains both source tokens even though only the first contributes an error.
-/
theorem two_failure_replay_pendingAccounting
    : ((State.initialize (Work.fromExecution work)).runNormalized
        [[first], [second]]).1.PendingAccounting
        work [secondTask, firstTask] := by
  exact generated.runNormalized_pendingLedger [[first], [second]]
    (source_valid.prefix ⟨[finish], rfl⟩) (by cbv)

/-- The same invariant survives the later parent success and delayed-failure drain.
Witness: the general replay theorem covers the complete original source sequence.
-/
theorem complete_replay_pendingAccounting
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.PendingAccounting
        work (GraphEvent.taskSettlements inputs.flatten) :=
  generated.runNormalized_pendingLedger inputs source_valid inputs_started

/-- Healthy counters remain exact after a cancelled source failure is ignored.
Witness: the general healthy replay theorem applied to the same prefix that disproves
exact all-group accounting. Both failures are recorded for health, but neither is a
successful settlement, so the success-only ledger is still empty.
-/
theorem two_failure_replay_healthyCounters
    : ((State.initialize (Work.fromExecution work)).runNormalized
        [[first], [second]]).1.HealthyPendingTracks
        work [] [secondTask, firstTask] := by
  exact (generated.runNormalized_healthyPendingAndLinks [[first], [second]]
          (source_valid.prefix ⟨[finish], rfl⟩) (by cbv)).1

/-- Parent release and the retained-error drain preserve healthy counter exactness too.
Witness: the general replay theorem covers every handler in the complete source history.
-/
theorem complete_replay_healthyCounters
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.HealthyPendingTracks
        work (GraphEvent.groupSettlements inputs.flatten)
        (GraphEvent.failureSettlements inputs.flatten) :=
  (generated.runNormalized_healthyPendingAndLinks inputs source_valid inputs_started).1

/-- Every healthy registered owner survives the active and ignored failure settlements.
Witness: unconditional generated replay derives ownership and retired ancestry from source
validity and the unchanged start check, with no availability or output-admission premise.
-/
theorem two_failure_replay_healthyOwners
    : ((State.initialize (Work.fromExecution work)).runNormalized
        [[first], [second]]).1.HealthyRegisteredTaskAccounting
        work [] [secondTask, firstTask] := by
  exact (generated.runNormalized_healthyRegisteredOwners [[first], [second]]
          (source_valid.prefix ⟨[finish], rfl⟩) (by cbv)).2

/-- The later successful parent and retained-failure drain preserve owner accounting.
Witness: the same general replay theorem applies to the complete source history.
-/
theorem complete_replay_healthyOwners
    : State.HealthyRegisteredTaskAccounting
        ((State.initialize (Work.fromExecution work)).runNormalized inputs).1
        work (GraphEvent.groupSettlements inputs.flatten)
        (GraphEvent.failureSettlements inputs.flatten) :=
  (generated.runNormalized_healthyRegisteredOwners inputs source_valid inputs_started).2

-----------------------------------------------------------------------------------------
-- The generated replay distinguishes source outcomes from error contributions
-----------------------------------------------------------------------------------------

/-- Only the first failure contributes; the ignored second settlement stays out of totals.
Witness: reduce the proof-side projection over the unchanged actual handler replay.
-/
theorem contributing_failures
    : (State.initialize (Work.fromExecution work)).objectFailureContributions
        inputs.flatten
      = [firstTask] := by
  cbv

/-- Dropping the ignored token leaves every group with the same invalidation status.
Witness: the general generated-source ledger equivalence, not this fixture's admitted
output witness or a case analysis over its group refs.
-/
theorem contributing_failures_health (ref : NodeRef)
    : GroupInvalidated work [secondTask, firstTask] ref
      ↔ GroupInvalidated work [firstTask] ref := by
  have same := generated.inputsStarted_objectFailureContributions source_valid
    inputs_started ref
  rw [contributing_failures] at same
  exact same

/-- The ignored second task is already cancelled by the first eligible failure alone.
Witness: the unconditional replay cancellation theorem at the one-failure boundary;
this boundary has no successful publication and requires no admitted-output premise.
-/
theorem second_cancelled_from_replay
    : Causality.TaskCancelled work [firstTask] (fun _ => False) secondTask := by
  have cancelled := generated.runNormalized_rejectedTask_cancelled
    (batches := [[first]]) (source_valid.prefix ⟨[second, finish], rfl⟩) (by cbv)
    (taskNode := { task := ⟨secondTask, [root, child, nested]⟩ })
    (occurrence := secondTask) (published := fun _ => False)
    (by cbv)
    (by simp [GraphEvent.taskSettlements, GraphEvent.groupSuccesses,
      GraphEvent.groupFailures, first, firstTask, secondTask])
    (by cbv) (by simp)
  have onlyFirst : (State.initialize (Work.fromExecution work)).objectFailureContributions
      [[first]].flatten = [firstTask] := by cbv
  rw [onlyFirst] at cancelled
  exact cancelled

/-- The ignored task is cancelled against an actual output matching, not a false predicate.
Witness: the general normalized-matching theorem derives nonpublication from fixed failed
payloads, then replay accounting supplies the earlier eligible failure cause.
-/
theorem second_cancelled_with_outputMatching
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first]]).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ Causality.TaskCancelled work [firstTask] (Published matching atoms)
            secondTask := by
  obtain ⟨matching, batching, _, cancelled⟩ := generated.runNormalized_rejectedFailures_matching
    (batches := [[first]]) (source_valid.prefix ⟨[second, finish], rfl⟩) (by cbv)
  refine ⟨matching, batching, ?_⟩
  have result := cancelled secondTask { task := ⟨secondTask, [root, child, nested]⟩ } 2
    ⟨_, _, _, second_known⟩ (by cbv)
    (by simp [GraphEvent.taskSettlements, GraphEvent.groupSuccesses,
      GraphEvent.groupFailures, first, firstTask, secondTask]) (by cbv)
  have onlyFirst : (State.initialize (Work.fromExecution work)).objectFailureContributions
      [[first]].flatten = [firstTask] := by cbv
  rwa [onlyFirst] at result

/-- Reversing the failures keeps both contributions because D still makes A eligible.
Witness: the same projection checks the actual guard at each reversed settlement state.
-/
theorem reversed_contributing_failures
    : (State.initialize (Work.fromExecution work)).objectFailureContributions
        [second, first, finish]
      = [firstTask, secondTask] := by
  cbv

/-- Surviving caches count the eligible failure, not both received source failures.
Witness: general generated replay error accounting; the only fixture-specific step is
evaluating the guard-filtered ledger at this two-input boundary.
-/
theorem two_failure_replay_errorAccounting
    : State.GroupErrorAccounting
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
        work [firstTask] := by
  have counts := generated.runNormalized_groupErrorAccounting [[first], [second]]
    (source_valid.prefix ⟨[finish], rfl⟩) (by cbv)
  have selected : (State.initialize (Work.fromExecution work)).objectFailureContributions
      [[first], [second]].flatten = [firstTask] := by cbv
  rwa [selected] at counts

/-- The delayed child completion's one error has exactly the eligible contributor set.
Witness: general next-handler output accounting after generated started replay, with the
actual child failure selected from the parent's successful release and recursive drain.
Neither output admission nor an independently chosen per-completion subset is assumed.
-/
theorem child_error_from_replay : NodeErrors work [firstTask] child.ref 1 := by
  obtain ⟨_, matching, _⟩ := validGraphEvents_last
    (before := [first, second]) (event := finish) source_valid
  have count := generated.runNormalized_groupFailure_nodeErrors [[first], [second]]
    (source_valid.prefix ⟨[finish], rfl⟩) (by cbv) finish matching
    (group := child) (errors := 1) (by cbv; exact .tail _ (.tail _ (.head _)))
  have selected : (State.initialize (Work.fromExecution work)).objectFailureContributions
      [[first], [second]].flatten = [firstTask] := by cbv
  rw [selected] at count
  exact count

/-- The complete replay keeps exact error accounting after the parent drains its children.
Witness: generated normalized replay uses the same eligible ledger across every handler.
-/
theorem complete_replay_errorAccounting
    : State.GroupErrorAccounting
        ((State.initialize (Work.fromExecution work)).runNormalized inputs).1 work
        [firstTask] := by
  have counts := generated.runNormalized_groupErrorAccounting inputs source_valid inputs_started
  rwa [contributing_failures] at counts

/-- Ignored settlement and later recursive release preserve duplicate-free child links.
Witness: the general concrete-bookkeeping theorem, independent of source validity.
-/
theorem replay_childLinks_unique
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.ChildGroupsUnique :=
  createWorkQueue_runNormalized_childGroupsUnique _ _

/-- Removing a retained failed parent still visits its live child after ignored settlement.
Witness: the general generated-replay traversal theorem applied to the actual D-to-E link;
the child may have a surplus pending count, but that does not weaken traversal coverage.
-/
theorem retained_parent_removal_covers_child
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
      (queue.removeGroup other.ref).groupNode? nested.ref = none
      ∧ nested.ref ∉ (queue.removeGroup other.ref).rootGroups := by
  apply generated.runNormalized_removeGroup_covers [[first], [second]]
    (source_valid.prefix ⟨[finish], rfl⟩)
  apply State.LiveDescendant.child (child := nested.ref)
  · cbv
  · simp [nested]
  · exact .self (by cbv)

private def eligibleCandidateCuts : FailureCuts :=
  let queue := State.initialize (Work.fromExecution work)
  let blocks :=
    (queue.sourceRunBlocks
      { active := queue.initialGroups ++ queue.initialStreams } inputs).2.2
  sourceObjectFailureCuts 0 (queue.eligibleFailureBlocks blocks)

/-- The actual normalized candidate list omits the ignored second failure.
Witness: guard-selected source labels retain every output block but record only A's cut.
-/
theorem eligible_candidate_cuts : eligibleCandidateCuts = [(0, firstTask)] := by cbv

/-- The delayed child total counts exactly the eligible cuts at its actual output index.
Witness: general complete normalized error accounting, not the hand-built admitted run.
-/
theorem child_error_at_eligible_cut
    : NodeErrors work (failedBefore eligibleCandidateCuts 3) child.ref 1 := by
  apply createWorkQueue_sourceObjectFailureCuts_nodeErrors generated source_valid inputs_started
    (batches := inputs) (group := child)
  rw [output]
  rfl

/-- General generated replay constructs a complete failure inventory for the corrected run.
Witness: the mixed object/stream inventory theorem; no output admission is supplied.
Open-owner and cancellation licensing are not conclusions of this inventory certificate.
-/
theorem complete_candidate_inventory
    : ∃ cuts : FailureCuts,
        CompleteFailureInventory work
          (((State.initialize (Work.fromExecution work)).runNormalized
              inputs).2.flatten.flatMap
            publicationAtoms) cuts :=
  createWorkQueue_completeFailureInventory_exists generated source_valid inputs_started

/-- Ignoring the second task can leave a failed group with surplus pending tokens.
Witness: C retains counter one after its last membership disappears. Thus the old exact
all-group ledger is false even though `second_pendingBound` establishes counter safety.
-/
theorem second_not_pendingTracks
    : let queue := ((State.initialize (Work.fromExecution work)).handleGraphEvent first).1
      ¬(queue.handleGraphEvent second).1.PendingTracks [secondTask, firstTask] := by
  dsimp only
  intro exactCounts
  let node : GroupNode :=
    { group := { node := child, parent := some parent.ref }, pending := 1,
      failure := some 1 }
  have member : node ∈
      ((((State.initialize (Work.fromExecution work)).handleGraphEvent first).1).handleGraphEvent
        second).1.groupNodes := by
    dsimp only [node]
    cbv
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have count := exactCounts node member
  simp [GroupNode.PendingTracks, node, unsettledCount] at count

/-- Reversed settlements still accumulate errors while D is a healthy surviving owner.
Witness: the second partition settles first; D keeps the first partition eligible.
-/
theorem reversed_output
    : inputsStarted work [[second], [first], [finish]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[second], [first], [finish]]).2
        = [
          [.groupFailure root 2],
          [
            .groupValues parent
              [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
            .groupSuccess parent [child, other] [],
            .groupFailure child 3,
            .groupFailure other 1,
            .workQueueTermination
          ]
        ] := by
  cbv

/-- Every structural task is one of the two failures or the successful parent.
Witness: membership in the finite structural observation-token inventory.
-/
private theorem task_cases {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = firstTask ∨ occurrence = secondTask ∨ occurrence = parentTask := by
  have member := known.observationToken
  simpa [observationTokens, work, firstTask, secondTask, parentTask] using member

/-- Every node descriptor is one of the five named groups, including repeated owners.
Witness: group-only structural roles and the three possible execution-group locations.
-/
private theorem node_cases {node kind dependencies producer}
    (known : NodeAt work node kind dependencies producer)
    : node = root ∨ node = child ∨ node = other ∨ node = nested ∨ node = parent := by
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have groupKind : kind = .group := by
    have role := Correctness.node_ref_role roles known
    cases kind with
    | group => rfl
    | stream => change false = true at role; cases role
  subst kind
  obtain ⟨address, groups, path, result, children, enclosing, group,
    located, member, rfl, _⟩ := known
  have task : TaskAt work (.executionGroup address)
      (groups.map (fun group => group.node.ref)) producer (.object path result) :=
    ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩
  rcases task_cases task with same | same | same
  · have addressEq := Occurrence.executionGroup.inj same
    change address = [1, 0] at addressEq
    subst address
    have equal : groups = [⟨root, []⟩, ⟨child, [parent]⟩, ⟨other, [parent]⟩] := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact equal.1.1
    rw [equal] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp
  · have addressEq := Occurrence.executionGroup.inj same
    change address = [1, 1, 0] at addressEq
    subst address
    have equal : groups = [⟨root, []⟩, ⟨child, [parent]⟩, ⟨nested, [other, parent]⟩] := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact equal.1.1
    rw [equal] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp
  · have addressEq := Occurrence.executionGroup.inj same
    change address = [1, 1, 1, 0] at addressEq
    subst address
    have equal : groups = [⟨parent, []⟩] := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact equal.1.1
    rw [equal] at member
    have same := List.mem_singleton.mp member
    subst group
    simp

/-- Repeated group refs retain identical node metadata, as public conformance requires.
Witness: the finite descriptor classification and distinct refs of the five groups.
-/
theorem coherent : NodeRefCoherent work := by
  intro left leftKind leftDependencies leftProducer right rightKind rightDependencies
    rightProducer leftKnown rightKnown sameRef
  rcases node_cases leftKnown with rfl | rfl | rfl | rfl | rfl
    <;> rcases node_cases rightKnown with rfl | rfl | rfl | rfl | rfl
    <;> simp_all [root, child, other, nested, parent]

/-- The actual initial notices meet the independent initialization contract.
Witness: R and P are fresh root groups, each with an outstanding unpublished task.
-/
theorem initialized
    : let queue := State.initialize (Work.fromExecution work)
      Initializes work queue.initialGroups queue.initialStreams := by
  have eligible {node occurrence owners payload}
      (known : TaskAt work occurrence owners none payload) (owner : node.ref ∈ owners)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
    refine ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨by simp [NodeFailed], Or.inr ?_⟩, by simp, by simp⟩
    intro accounted
    rcases accounted occurrence owners ⟨_, _, known⟩ owner with cancelled | published
    · simp [TaskCancelled] at cancelled
    · simp [Published] at published
  change Initializes work [root, parent] []
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  rcases List.mem_cons.mp member with same | last
  · subst node
    exact ⟨[], none,
      ⟨[1, 0], _, [], .error 1, .empty, [], ⟨root, []⟩, rfl, by simp, rfl, rfl⟩,
      eligible first_known (by simp)⟩
  · have same := List.mem_singleton.mp last
    subst node
    exact ⟨[], none,
      ⟨[1, 1, 1, 0], _, [], .ok (data, 0), .combine .empty .empty, [],
        ⟨parent, []⟩, rfl, by simp, rfl, rfl⟩,
      eligible parent_known (by simp)⟩

-----------------------------------------------------------------------------------------
-- Exact error counts force an impossible causal ordering
-----------------------------------------------------------------------------------------

/-- R's one-error completion must record the first task, and cannot record the second.
Witness: the second contributes at least two errors; without either task every sum is zero.
-/
private theorem root_count {failed} (counted : NodeErrors work failed root.ref 1)
    : firstTask ∈ failed ∧ secondTask ∉ failed := by
  have absent : secondTask ∉ failed := by
    intro member
    have bound := counted.contribution_le member second_known (by simp)
    change 2 ≤ 1 at bound
    omega
  refine ⟨?_, absent⟩
  apply Classical.byContradiction
  intro noFirst
  obtain ⟨contribution, values, total⟩ := counted
  have zero : ∀ occurrence ∈ failed, contribution occurrence = 0 := by
    intro occurrence member
    obtain ⟨owners, producer, payload, known, assigned⟩ := values occurrence member
    rcases task_cases known with rfl | rfl | rfl
    · exact False.elim (noFirst member)
    · exact False.elim (absent member)
    · obtain ⟨rfl, _, rfl⟩ := known.unique parent_known
      simpa [Payload.failure, root, parent] using assigned
  have sumZero : (failed.map contribution).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro count member
    obtain ⟨occurrence, included, rfl⟩ := List.mem_map.mp member
    exact zero occurrence included
  omega

/-- A unique failure inventory lacking the second task reports at most one error for C.
Witness: the first task is its only remaining nonzero summand and cannot be duplicated.
-/
private theorem child_requires_second {failed}
    (unique : failed.Nodup) (counted : NodeErrors work failed child.ref 3)
    : secondTask ∈ failed := by
  apply Classical.byContradiction
  intro absent
  obtain ⟨contribution, values, total⟩ := counted
  have valuesEq : ∀ occurrence ∈ failed,
      contribution occurrence = if occurrence = firstTask then 1 else 0 := by
    intro occurrence member
    obtain ⟨owners, producer, payload, known, assigned⟩ := values occurrence member
    rcases task_cases known with rfl | rfl | rfl
    · obtain ⟨rfl, _, rfl⟩ := known.unique first_known
      simpa [Payload.failure] using assigned
    · exact False.elim (absent member)
    · obtain ⟨rfl, _, rfl⟩ := known.unique parent_known
      simpa [Payload.failure, parentTask, firstTask, child, parent] using assigned
  have bound : (failed.map contribution).sum ≤ 1 := by
    rw [List.map_congr_left valuesEq]
    have go (more : List Occurrence) (distinct : more.Nodup)
        : (more.map (fun occurrence => if occurrence = firstTask then 1 else 0)).sum ≤ 1 := by
      induction more with
      | nil => simp
      | cons occurrence rest ih =>
          have fresh := List.nodup_cons.mp distinct
          by_cases same : occurrence = firstTask
          · subst occurrence
            have zeros : rest.map (fun occurrence => if occurrence = firstTask then 1 else 0)
                = rest.map (fun _ => 0) := by
              apply List.map_congr_left
              intro occurrence member
              have different : occurrence ≠ firstTask := by
                intro equal
                exact fresh.1 (equal ▸ member)
              simp [different]
            have sumZero : (rest.map (fun _ => (0 : Nat))).sum = 0 := by
              apply List.sum_eq_zero_iff_forall_eq_nat.mpr
              simp
            simp [zeros, sumZero]
          · simpa [same] using ih fresh.2
    exact go failed unique
  omega

private theorem nested_node : NodeAt work nested .group [other.ref, parent.ref] none :=
  ⟨
    [1, 1, 0],
    _,
    [],
    .error 2,
    .empty,
    [],
    ⟨nested, [other, parent]⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

/-- Once the first failure is recorded, every owner of the second task has failed.
Witness: R and C directly share the first task; E inherits failure through its ancestor D.
This is stronger than failure of just the task's shared latent owner C.
-/
private theorem second_cancelled {matching events before cut}
    (recorded : (cut, firstTask) ∈ before) (reached : cut ≤ events.length)
    (unpublished : ¬Published matching events secondTask)
    : TaskCancelled work matching events before secondTask := by
  have failed : firstTask ∈ failedBefore before cut :=
    mem_failedBefore recorded (Nat.le_refl _)
  refine ⟨
    cut,
    List.mem_map.mpr ⟨_, recorded, rfl⟩,
    reached,
    Causality.TaskCancelled.owners ⟨_, _, second_known⟩ ?_ (by simp) ?_
  ⟩
  · intro published
    apply unpublished
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  · intro ref member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .task ⟨_, _, first_known⟩ (by simp) failed
    · exact .task ⟨_, _, first_known⟩ (by simp) failed
    · exact .groupDependency (dependency := other.ref) ⟨nested, none, nested_node, rfl⟩ (by simp)
        (.task ⟨_, _, first_known⟩ (by simp) failed)

/-- No explained history can emit R's one-error closure and C's three-error closure.
Witness: R forces the first task before the second. C needs the second task too, but
the first cut already cancels it through all owners, contradicting failure licensing.
-/
theorem closure_counts_unexplained {events : List Execution.WorkQueueEvent}
    {matching failures} {i j : Nat} (atRoot : events[i]? = some (.groupFailure root 1))
    (atChild : events[j]? = some (.groupFailure child 3))
    : ¬Explains work [root, parent] [] events matching failures := by
  intro explained
  have rootAllowed := explained.2.2 i _ atRoot
  have childAllowed := explained.2.2 j _ atChild
  simp only [EventAllowed, failedBefore_filter _ (Nat.le_refl _)] at rootAllowed childAllowed
  obtain ⟨firstRecorded, noSecond⟩ := root_count rootAllowed.2.2.2
  have unique : (failedBefore failures (events.take j).length).Nodup :=
    explained.failures_nodup.sublist (List.filter_sublist.map Prod.snd)
  have secondRecorded := child_requires_second unique childAllowed.2.2.2
  obtain ⟨⟨firstCut, firstOccurrence⟩, firstKept, sameFirst⟩ := List.mem_map.mp firstRecorded
  obtain ⟨firstMember, firstBound⟩ := List.mem_filter.mp firstKept
  dsimp only at sameFirst
  subst firstOccurrence
  obtain ⟨⟨secondCut, secondOccurrence⟩, secondKept, sameSecond⟩ := List.mem_map.mp secondRecorded
  obtain ⟨secondMember, _⟩ := List.mem_filter.mp secondKept
  dsimp only at sameSecond
  subst secondOccurrence
  have earlier : firstCut < secondCut := by
    have bound : firstCut ≤ (events.take i).length := of_decide_eq_true firstBound
    by_cases late : (events.take i).length < secondCut
    · omega
    · exact False.elim (noSecond (mem_failedBefore secondMember (by omega)))
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp secondMember
  have prior : (firstCut, firstTask) ∈ before := by
    rw [split] at firstMember
    rcases List.mem_append.mp firstMember with prior | later
    · exact prior
    · rcases List.mem_cons.mp later with same | later
      · have equal := (Prod.mk.inj same).1
        omega
      · obtain ⟨middle, rest, afterEq⟩ := List.mem_iff_append.mp later
        have firstSplit : failures = (before ++ (secondCut, secondTask) :: middle)
            ++ (firstCut, firstTask) :: rest := by
          simp only [split, afterEq, List.append_assoc, List.cons_append]
        have bound := (explained.2.1 _ firstCut firstTask rest firstSplit).2.1
          (secondCut, secondTask) (by simp)
        dsimp only at bound
        omega
  have license := explained.2.1 before secondCut secondTask after split
  apply license.2.2.2
  apply second_cancelled prior
  · simp only [List.length_take, Nat.min_eq_left license.1]
    exact Nat.le_of_lt earlier
  · intro published
    have full : Published matching events secondTask := by
      simpa only [List.take_append_drop] using published.append (events.drop secondCut)
    have impossible := explained.published_succeeds second_known full
    cases impossible

-----------------------------------------------------------------------------------------
-- Rebatching or changing the publication matching cannot repair the output
-----------------------------------------------------------------------------------------

/-- Keep group-failure controls; batching may combine values but not these controls. -/
private def isGroupFailure : Execution.WorkQueueEvent → Bool
  | .groupFailure .. => true
  | _ => false

/-- Compatible value events cannot be failed completions.
Witness: inspect the two compatible value constructors and their combined result.
-/
private theorem combine_failureControls {left right merged}
    (compatible : combineValues left right = some merged)
    : isGroupFailure left = false
      ∧ isGroupFailure right = false
      ∧ isGroupFailure merged = false := by
  cases left <;> cases right <;> simp only [combineValues] at compatible
    <;> try contradiction
  all_goals split at compatible
  all_goals cases compatible
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- Every permitted value grouping retains the same group-failure controls.
Witness: induction over separate and coalesced values, preserving counts and order.
-/
private theorem grouping_failureControls {events grouped}
    (grouping : ValueGrouping events grouped)
    : events.filter isGroupFailure = grouped.filter isGroupFailure := by
  induction grouping with
  | nil => rfl
  | separate head _ ih => simp only [List.filter_cons]; split <;> simp_all
  | combine head _ compatible ih =>
      obtain ⟨left, right, merged⟩ := combine_failureControls compatible
      simpa only [List.filter_cons, left, right, merged, Bool.false_eq_true,
        ite_false] using ih

/-- Every permitted batch partition retains the same group-failure controls.
Witness: distribute filtering over the per-batch grouping equations.
-/
private theorem batching_failureControls {events batches}
    (batching : WorkBatching events batches)
    : events.filter isGroupFailure = batches.flatten.filter isGroupFailure := by
  induction batching with
  | nil => rfl
  | cons _ values _ ih =>
      simp only [List.flatten_cons, List.filter_append, grouping_failureControls values, ih]

/-- Preserving the runner's failure controls forces both incompatible count statements.
Witness: recover their event indices from filter membership, independently of batching.
-/
private theorem output_controls_unexplained {events matching failures}
    (same : events.filter isGroupFailure = outputs.flatten.filter isGroupFailure)
    : ¬Explains work [root, parent] [] events matching failures := by
  have rootMember : Execution.WorkQueueEvent.groupFailure root 1 ∈ events := by
    have selected : Execution.WorkQueueEvent.groupFailure root 1 ∈ events.filter isGroupFailure := by
      rw [same]
      simp [outputs, isGroupFailure]
    exact (List.mem_filter.mp selected).1
  have childMember : Execution.WorkQueueEvent.groupFailure child 3 ∈ events := by
    have selected : Execution.WorkQueueEvent.groupFailure child 3 ∈ events.filter isGroupFailure := by
      rw [same]
      simp [outputs, isGroupFailure]
    exact (List.mem_filter.mp selected).1
  obtain ⟨i, atRoot⟩ := List.mem_iff_getElem?.mp rootMember
  obtain ⟨j, atChild⟩ := List.mem_iff_getElem?.mp childMember
  exact closure_counts_unexplained atRoot atChild

/-- No alternate matching, failure-cut placement, or value batching admits this output.
Witness: all batchings retain R's one-error and C's three-error controls, whose forced
failure order violates cancellation licensing. Both interrupted and complete histories
are rejected by the unchanged scheduler contract.
-/
theorem output_not_valid : ¬ValidHistory work ⟨[root, parent], [], outputs⟩ := by
  rintro (⟨events, matching, failures, explained, batching⟩ |
    ⟨events, matching, failures, explained, _, batching⟩)
  · exact output_controls_unexplained (batching_failureControls batching) explained
  · have same := batching_failureControls batching
    simp only [List.filter_append, isGroupFailure, List.filter_cons_of_neg,
      Bool.false_eq_true, not_false_eq_true, List.filter_nil, List.append_nil] at same
    exact output_controls_unexplained same explained

/-- The corrected runner no longer produces the universally rejected error counts.
Witness: actual replay completes C with one error, rather than the former three.
-/
theorem runner_avoids_rejected_output
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
      ≠ outputs := by
  rw [output]
  simp [correctedOutputs, outputs]

-----------------------------------------------------------------------------------------
-- The corrected runner has a complete explanation under the unchanged contract
-----------------------------------------------------------------------------------------

private def matching : PublicationMatching := fun _ => parentTask
private def failures : FailureCuts := [(0, firstTask)]
private def initial : NodeRefs := [root.ref, parent.ref]

private def events : List Execution.WorkQueueEvent :=
  [
    .groupFailure root 1,
    .groupValues parent
      [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
    .groupSuccess parent [child, other] [],
    .groupFailure child 1,
    .groupFailure other 1
  ]

private theorem root_node : NodeAt work root .group [] none :=
  ⟨[1, 0], _, [], .error 1, .empty, [], ⟨root, []⟩, rfl, by simp, rfl, rfl⟩

private theorem parent_node : NodeAt work parent .group [] none :=
  ⟨
    [1, 1, 1, 0],
    _,
    [],
    .ok (data, 0),
    .combine .empty .empty,
    [],
    ⟨parent, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

private theorem child_node : NodeAt work child .group [parent.ref] none :=
  ⟨[1, 0], _, [], .error 1, .empty, [], ⟨child, [parent]⟩, rfl, by simp, rfl, rfl⟩

private theorem other_node : NodeAt work other .group [parent.ref] none :=
  ⟨[1, 0], _, [], .error 1, .empty, [], ⟨other, [parent]⟩, rfl, by simp, rfl, rfl⟩

/-- The only retained failure cannot invalidate the independent successful parent.
Witness: the generated root-group criterion excludes both contributors and ancestry.
-/
private theorem parent_healthy (observed : List Execution.WorkQueueEvent)
    : ¬NodeFailed work matching observed failures parent.ref := by
  rintro ⟨cut, member, _, cause⟩
  have zero : cut = 0 := by simpa [failures] using member
  subst cut
  apply generated.rootProducedGroup_healthy parent_node ?_ (by simp) cause
  intro occurrence recorded owners known owner
  have same : occurrence = firstTask := by simpa [failedBefore, failures] using recorded
  subst occurrence
  obtain ⟨producer, payload, known⟩ := known
  obtain ⟨rfl, _, _⟩ := known.unique first_known
  simp [root, parent, child, other] at owner

/-- P cannot be cancelled through either its healthy owner or its absent producer.
Witness: task descriptor uniqueness and the independent parent's health.
-/
private theorem parent_uncancelled (observed : List Execution.WorkQueueEvent)
    : ¬TaskCancelled work matching observed failures parentTask := by
  rintro ⟨cut, member, bound, cause⟩
  have zero : cut = 0 := by simpa [failures] using member
  subst cut
  cases cause with
  | owners known _ _ failed =>
      obtain ⟨producer, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique parent_known
      exact parent_healthy observed ⟨0, member, bound, failed parent.ref (by simp)⟩
  | producerFailed known _ _ | producerCancelled known _ _ =>
      obtain ⟨owners, payload, known⟩ := known
      cases (known.unique parent_known).2.1

/-- One recorded task supplies exactly one error to each of R, C, and D.
Witness: its singleton contribution; the cancelled second task is not recorded.
-/
private theorem first_errors {ref} (owner : ref ∈ [root.ref, child.ref, other.ref])
    : NodeErrors work [firstTask] ref 1 := by
  refine ⟨fun _ => 1, ?_, rfl⟩
  intro occurrence member
  have same := List.mem_singleton.mp member
  subst occurrence
  exact ⟨_, _, _, first_known, by simp [owner, Payload.failure]⟩

/-- The first task's failure is licensed by the initially open R group.
Witness: one root-produced failure at cut zero, before any cancellation is recorded.
-/
private theorem failure_licensed
    : FailureWitness work initial matching events failures := by
  intro before cut occurrence after equal
  have sizes := congrArg List.length equal
  simp only [failures, List.length_append, List.length_cons, List.length_nil] at sizes
  have emptyBefore : before = [] := List.eq_nil_of_length_eq_zero (by omega)
  have emptyAfter : after = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst before
  subst after
  have same : (0, firstTask) = (cut, occurrence) := by simpa [failures] using equal
  cases same
  refine ⟨by decide, by simp, ?_, by simp [TaskCancelled]⟩
  exact ⟨
    _,
    _,
    _,
    first_known,
    rfl,
    .root ⟨_, _, first_known⟩,
    root.ref,
    by simp,
    by decide
  ⟩

private theorem parent_published : Published matching (events.take 2) parentTask :=
  ⟨
    1,
    .groupValues parent
      [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
    rfl,
    trivial,
    rfl
  ⟩

/-- Normal parent completion can announce both retained failed children together.
Witness: the parent's prior publication and each child's first-task contribution.
-/
private theorem notice_allowed
    : EventAllowed work initial matching (events.take 2) failures
        (.groupSuccess parent [child, other] []) := by
  refine ⟨⟨[], none, parent_node⟩, by unfold Open; decide, parent_healthy _, ?_, ?_⟩
  · rintro occurrence owners ⟨producer, payload, known⟩ owner
    rcases task_cases known with rfl | rfl | rfl
    · obtain ⟨rfl, _, _⟩ := known.unique first_known
      simp [root, parent, child, other] at owner
    · obtain ⟨rfl, _, _⟩ := known.unique second_known
      simp [root, parent, child, nested] at owner
    · exact Or.inr parent_published
  · refine ⟨by decide, ?_, by simp⟩
    intro node member
    have notice (node : DeliveryNode) (known : NodeAt work node .group [parent.ref] none)
        (fresh : node.ref ∉ announcedRefs initial
          (events.take 2 ++ [.groupSuccess parent [] []]))
        (owner : node.ref ∈ [root.ref, child.ref, other.ref])
        : ∃ dependencies producer, NodeAt work node .group dependencies producer
            ∧ CanAnnounce work initial matching
              (events.take 2 ++ [.groupSuccess parent [] []]) failures
              node .group dependencies producer := by
      refine ⟨[parent.ref], none, known, fresh, Or.inr ?_, by simp, ?_⟩
      · exact ⟨rfl, firstTask, _, by simp [failedBefore, failures],
          ⟨_, _, first_known⟩, owner⟩
      · intro ref member
        have same := List.mem_singleton.mp member
        subst ref
        exact ⟨parent_healthy _, Or.inr (Or.inl (by decide))⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact notice child child_node (by decide) (by simp)
    · have same := List.mem_singleton.mp member
      subst node
      exact notice other other_node (by decide) (by simp)

/-- Each corrected output atom is admitted with just the first failure recorded.
Witness: a single parent publication, normal child notices, and one-error closures.
-/
theorem atomic_explanation
    : Explains work [root, parent] [] events matching failures := by
  refine ⟨initialized, failure_licensed, ?_⟩
  intro index event selected
  match index with
  | 0 =>
      cases selected
      refine ⟨⟨[], none, root_node⟩, by unfold Open; decide, ?_, first_errors (by simp)⟩
      exact NodeFailed.task first_known (by simp) (by simp [failedBefore, failures])
  | 1 =>
      cases selected
      refine ⟨[parent.ref], none,
        { path := [], data := data, deliveryGroups := [parent] },
        rfl, parent_known, ?_, ?_⟩
      · refine ⟨?_, parent_uncancelled _, by simp, trivial⟩
        rintro ⟨index, event, selected, value, _⟩
        cases index with
        | zero => cases selected; exact value
        | succ index => simp [events] at selected
      · have opened : OpenOwner work initial (events.take 1) [parent.ref] parent :=
          ⟨⟨.group, [], none, parent_node⟩, by simp, by unfold Open; decide⟩
        refine ⟨opened, ⟨parent, opened, parent_healthy _⟩, ?_⟩
        intro owner available
        obtain ⟨kind, dependencies, producer, known⟩ := available.1
        rcases node_cases known with rfl | rfl | rfl | rfl | rfl <;> decide
  | 2 => cases selected; exact notice_allowed
  | 3 =>
      cases selected
      refine ⟨
        ⟨[parent.ref], none, child_node⟩,
        by unfold Open; decide,
        ?_,
        first_errors (by simp)
      ⟩
      exact NodeFailed.task first_known (by simp) (by simp [failedBefore, failures])
  | 4 =>
      cases selected
      refine ⟨
        ⟨[parent.ref], none, other_node⟩,
        by unfold Open; decide,
        ?_,
        first_errors (by simp)
      ⟩
      exact NodeFailed.task first_known (by simp) (by simp [failedBefore, failures])
  | index + 5 => simp [events] at selected

/-- The late task is accounted for by cancellation, not a second licensed failure.
Witness: the first cut invalidates R/C/D and E through D; P is published and E unannounced.
-/
private theorem terminal : Terminal work initial matching events failures := by
  constructor
  · intro occurrence owners producer payload known
    rcases task_cases known with rfl | rfl | rfl
    · apply Or.inl
      refine ⟨0, by simp [failures], by simp, ?_⟩
      apply Causality.TaskCancelled.owners ⟨_, _, first_known⟩
        (by simp [Published]) (by simp)
      intro ref member
      exact .task ⟨_, _, first_known⟩ member (by simp [failedBefore, failures])
    · apply Or.inl
      apply second_cancelled (cut := 0) (by simp [failures]) (by simp)
      rintro ⟨_, _, _, _, same⟩
      simp [matching, parentTask, secondTask] at same
    · exact Or.inr ⟨1, .groupValues parent [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }], rfl, trivial, rfl⟩
  · intro node kind dependencies producer known
    rcases node_cases known with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · refine Or.inr ⟨by decide, Or.inl ?_⟩
      refine ⟨0, by simp [failures], by simp, ?_⟩
      exact .groupDependency (dependency := other.ref) ⟨nested, none, nested_node, rfl⟩
        (by simp) (.task ⟨_, _, first_known⟩ (by simp) (by simp [failedBefore, failures]))
    · exact Or.inl (by decide)

/-- The corrected generated runner satisfies complete WorkQueueSemantics admission here.
Witness: the coherent atomic explanation and terminal accounting with the actual batching.
-/
theorem output_admitted
    : AdmissibleRun work
        ⟨
          [root, parent],
          [],
          ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
        ⟩ := by
  rw [output]
  refine ⟨events, matching, failures, atomic_explanation, terminal, ?_⟩
  exact .cons (batch := [.groupFailure root 1]) (by simp) (.separate _ .nil)
    (.cons
      (batch :=
        [
          .groupValues parent
            [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
          .groupSuccess parent [child, other] [],
          .groupFailure child 1,
          .groupFailure other 1,
          .workQueueTermination
        ])
      (by simp) (.separate _ (.separate _ (.separate _ (.separate _ (.separate _ .nil)))))
      .nil)

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerCancelledFailure
