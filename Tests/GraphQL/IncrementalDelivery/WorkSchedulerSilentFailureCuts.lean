import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailurePlacement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootGroupCausality
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Silent settlements need not have an open owner at their source-block boundary. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerSilentFailureCuts
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def root : DeliveryNode := { key := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { key := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { key := 2, path := [], label := some (.string "C") }
private def firstTask : Occurrence := .executionGroup [1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def data : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨root, []⟩] [] (.error 1) .empty)
      (.combine (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] [] (.error 1) .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] (.ok (data, 0)) (.combine .empty .empty))
          .empty)))

private def first : GraphEvent := .taskFailure firstTask 1
private def shared : GraphEvent := .taskFailure sharedTask 1

private def finish : GraphEvent :=
  .taskSuccess parentTask
    {
      value := { deliveryGroups := [parent], path := [], data },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def inputs : List (List GraphEvent) := [[first], [shared], [finish]]

private def events : List Execution.WorkQueueEvent :=
  [
    .groupFailure root 1,
    .groupValues parent
      [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
    .groupSuccess parent [child] [],
    .groupFailure child 1,
    .workQueueTermination
  ]

private def candidateCuts : FailureCuts := [(0, firstTask), (1, sharedTask)]
private def initial : Keys := [root.key, parent.key]

/-- A root task and a shared root/latent-child task fail independently in generated work.
Witness: the shared response key belongs to both R and the child C under healthy P.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required", field "required" [] [] (some "shared")] (some "R"),
      defer [field "a", defer [field "required" [] [] (some "shared")] (some "C")]
        (some "P")], ?_⟩
  cbv

private theorem first_known
    : TaskAt work firstTask [root.key] none (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem shared_known
    : TaskAt work sharedTask [root.key, child.key] none (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem parent_known
    : TaskAt work parentTask [parent.key] none (.object [] (.ok (data, 0))) :=
  ⟨_, [], .ok (data, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩

/-- The shared task remains started after R closes, because latent C still owns it.
Witness: source freshness and fixed outcomes, together with the executable start checks.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have one : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, _, first_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first])
      ⟨_, _, _, first_known, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [first, shared] :=
    .append one ⟨_, _, _, shared_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first, shared, firstTask, sharedTask])
      ⟨_, _, _, shared_known, by intro source impossible; cases impossible⟩
  refine ⟨?_, by cbv⟩
  exact .append two ⟨_, _, parent_known, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, first, shared, finish,
      firstTask, sharedTask, parentTask])
    ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩

/-- The shared failure is silent until P releases C, whose completion reports its error.
Witness: direct queue/publisher evaluation, retaining the empty middle output batch.
-/
theorem output
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
      = [
        [.groupFailure root 1],
        [
          .groupValues parent
            [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
          .groupSuccess parent [child] [],
          .groupFailure child 1,
          .workQueueTermination
        ]
      ] := by cbv

/-- The source-block candidate records the silent shared failure at output index one.
Witness: exact source annotations; no event is emitted by that task's handler.
-/
theorem source_cuts
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      sourceObjectFailureCuts 0 (queue.sourceRunBlocks publisher inputs).2.2
      = candidateCuts := by cbv

/-- Both failures remain eligible: the shared task still has its healthy latent owner C.
Witness: the guard-selected annotation retains both labels without changing any output.
-/
theorem eligible_source_cuts
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      sourceObjectFailureCuts 0
        (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
      = candidateCuts := by cbv

/-- The complete source inventory nevertheless has correct counts at every failed closure.
Witness: the general inventory construction with no stream cuts, followed by exact replay.
-/
theorem candidate_inventory : CompleteFailureInventory work events candidateCuts := by
  have atomsEq : (((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
      publicationAtoms) = events := by cbv
  have cuts : StreamFailureCuts work
      (((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
        publicationAtoms) [] := by
    rw [atomsEq]
    exact ⟨rfl, by simp⟩
  have certificate := createWorkQueue_completeFailureInventory generated source_valid.1
    source_valid.2 cuts (by simp)
  have merged : mergeFailureCuts candidateCuts [] = candidateCuts := by cbv
  simpa only [eligible_source_cuts, merged, atomsEq] using certificate

/-- No owner is open at the silent settlement: R is closed and C is not yet announced.
Witness: the shared task's unique owner list and the exact Open predicate at index one.
Prior announcement nevertheless licenses this settlement under the revised contract.
-/
theorem source_cut_no_open_owner
    : ¬∃ key ∈ [root.key, child.key], Open initial (events.take 1) key := by
  rintro ⟨key, owner, opened⟩
  rcases List.mem_cons.mp owner with same | last
  · subst key
    have closed : root.key ∈ completedKeys (events.take 1) := by decide
    exact opened.2 closed
  · have same := List.mem_singleton.mp last
    subst key
    have unseen : child.key ∉ announcedKeys initial (events.take 1) := by decide
    exact unseen opened.1

/-- The general implementation theorem supplies C's prior notice at its delayed closure.
Witness: actual normalized output and the source-validity proof instantiate the generic
announcement law at unbatched index three, within the parent's release/drain batch.
-/
theorem child_failure_announced : child.key ∈ announcedKeys initial (events.take 3) := by
  have atomsEq : (((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
      publicationAtoms) = events := by cbv
  have initialEq :
      ((State.initialize (Work.fromExecution work)).initialGroups
        ++ (State.initialize (Work.fromExecution work)).initialStreams).map DeliveryNode.key
      = initial := by cbv
  have result := createWorkQueue_runNormalized_groupFailureAnnouncedAt source_valid.1
    (index := 3) (group := child) (errors := 1) (by rw [atomsEq]; rfl)
  simpa only [atomsEq, initialEq] using result

/-- Joining all host inputs into one batch keeps C's notice before its failed closure.
Witness: the same general atomic-output theorem, not a batching-specific admission premise.
-/
theorem child_failure_announced_single_batch
    : let queue := State.initialize (Work.fromExecution work)
      child.key
      ∈ announcedKeys
          ((queue.initialGroups ++ queue.initialStreams).map DeliveryNode.key)
          (((queue.runNormalized [inputs.flatten]).2.flatten.flatMap
              publicationAtoms).take
            3) := by
  have valid : ValidGraphEvents work [inputs.flatten].flatten := by
    simpa only [List.flatten_singleton] using source_valid.1
  exact createWorkQueue_runNormalized_groupFailureAnnouncedAt valid
    (index := 3) (group := child) (errors := 1) (by cbv)

/-- The delayed child closure has a prior notice and no earlier completion of its key.
Witness: the general retirement/role-separation theorem applied to this generated work,
without assuming a failure witness or admission of the output history.
-/
theorem child_failure_open : Open initial (events.take 3) child.key := by
  have atomsEq : (((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
      publicationAtoms) = events := by cbv
  have initialEq :
      ((State.initialize (Work.fromExecution work)).initialGroups
        ++ (State.initialize (Work.fromExecution work)).initialStreams).map DeliveryNode.key
      = initial := by cbv
  have result := createWorkQueue_runNormalized_groupFailureOpenAt generated source_valid.1
    (index := 3) (group := child) (errors := 1) (by rw [atomsEq]; rfl)
  simpa only [atomsEq, initialEq] using result

/-- Regrouping the host input preserves openness at the child's actual failed closure.
Witness: the same general theorem, including closures earlier in the one output batch.
-/
theorem child_failure_open_single_batch
    : let queue := State.initialize (Work.fromExecution work)
      Open ((queue.initialGroups ++ queue.initialStreams).map DeliveryNode.key)
        (((queue.runNormalized [inputs.flatten]).2.flatten.flatMap publicationAtoms).take
          3)
        child.key := by
  have valid : ValidGraphEvents work [inputs.flatten].flatten := by
    simpa only [List.flatten_singleton] using source_valid.1
  exact createWorkQueue_runNormalized_groupFailureOpenAt generated valid
    (index := 3) (group := child) (errors := 1) (by cbv)

/-- The successful parent and failed root/child each close exactly once in this output.
Witness: the generic closure-uniqueness theorem needs only matching source payloads.
-/
theorem group_closures_unique : (events.flatMap groupClosureKeys).Nodup := by
  have atomsEq : (((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
      publicationAtoms) = events := by cbv
  have result := createWorkQueue_runNormalized_atomicGroupClosuresUnique
    (fun _ member => source_valid.1.eachMatches member)
  simpa only [atomsEq] using result

-----------------------------------------------------------------------------------------
-- Delay proof recording until the surviving owner is announced; execution is unchanged
-----------------------------------------------------------------------------------------

private def delayedCuts : FailureCuts := [(0, firstTask), (3, sharedTask)]

/-- The general placement search selects the delayed cuts required by this silent failure.
Witness: R reports at zero; the shared failure's first later reporting owner is C at three.
-/
theorem reported_cuts : reportedFailureCuts work events candidateCuts = delayedCuts := by
  have firstSelected : firstReportedFailureCut work events (0, firstTask) = some 0 := by
    apply firstReportedFailureCut_eq_some (by decide)
      ⟨root, 1, .inl rfl, [root.key], ⟨_, _, first_known⟩, by simp⟩
    exact fun _ _ _ => Nat.zero_le _
  have sharedSelected : firstReportedFailureCut work events (1, sharedTask) = some 3 := by
    apply firstReportedFailureCut_eq_some (by decide)
      ⟨child, 1, .inl rfl, [root.key, child.key], ⟨_, _, shared_known⟩, by simp⟩
    intro index after report
    by_cases bound : 3 ≤ index
    · exact bound
    · have positions : index = 1 ∨ index = 2 := by omega
      rcases positions with rfl | rfl <;>
        obtain ⟨node, errors, atEvent, _⟩ := report <;>
        rcases atEvent with impossible | impossible <;> cases impossible
  simp only [reportedFailureCuts, candidateCuts, List.filterMap_cons, placeReportedFailure,
    firstSelected, sharedSelected, Option.map_some, List.filterMap_nil]
  exact List.mergeSort_of_pairwise (by simp)

/-- The general placement theorem preserves the full inventory at the delayed cuts.
Witness: first-report count preservation, instantiated using the checked candidate inventory.
-/
theorem delayed_inventory : CompleteFailureInventory work events delayedCuts := by
  rw [← reported_cuts]
  exact candidate_inventory.reported

/-- Before P releases C, the unreported shared failure can be omitted from count evidence.
Witness: the actual two-input prefix contains only R's closure; there is no later report
for the shared candidate. This asserts reported-count placement, not full cancellation safety.
-/
theorem unreported_failure_omitted
    : let observed :=
        (((State.initialize (Work.fromExecution work)).runNormalized
            [[first], [shared]]).2.flatten.flatMap
          publicationAtoms)
      reportedFailureCuts work observed candidateCuts = [(0, firstTask)] := by
  intro observed
  have output : observed = [.groupFailure root 1] := by dsimp only [observed]; cbv
  have firstSelected : firstReportedFailureCut work observed (0, firstTask) = some 0 := by
    apply firstReportedFailureCut_eq_some (by decide)
      ⟨root, 1, .inl (by rw [output]; rfl), [root.key], ⟨_, _, first_known⟩, by simp⟩
    exact fun _ _ _ => Nat.zero_le _
  have sharedSelected : firstReportedFailureCut work observed (1, sharedTask) = none := by
    apply firstReportedFailureCut_eq_none
    intro index after report
    have bound := report.bound
    rw [output] at bound
    simp only [List.length_singleton] at bound
    omega
  simp only [reportedFailureCuts, candidateCuts, List.filterMap_cons, placeReportedFailure,
    firstSelected, sharedSelected, Option.map_some, Option.map_none, List.filterMap_nil]
  exact List.mergeSort_singleton _

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

private theorem child_node : NodeAt work child .group [parent.key] none :=
  ⟨[1, 1, 0], _, [], .error 1, .empty, [], ⟨child, [parent]⟩, rfl, by simp, rfl, rfl⟩

/-- R's earlier failure does not causally fail healthy P or its latent child C.
Witness: neither key owns the failed task, and C's only dependency is healthy P.
-/
private theorem child_healthy (published : Occurrence → Prop)
    : ¬Causality.NodeFailed work [firstTask] published child.key := by
  have contributors {node : DeliveryNode} (different : node.key ≠ root.key)
      : ∀ occurrence ∈ [firstTask],
          ∀ owners, TaskHasOwners work occurrence owners → node.key ∉ owners := by
    intro occurrence member owners ⟨producer, payload, known⟩
    have same := List.mem_singleton.mp member
    subst occurrence
    rw [(known.unique first_known).1]
    simpa only [List.mem_singleton] using different
  have healthyParent := generated.rootProducedGroup_healthy (published := published) parent_node
    (contributors (by decide)) (by simp)
  apply generated.rootProducedGroup_healthy child_node (contributors (by decide))
  intro key member
  have same := List.mem_singleton.mp member
  subst key
  exact healthyParent

/-- The shared root task is not cancelled while C survives, even after R has closed.
Witness: cancellation would fail every owner, contradicting C's causal health; there
is no structural producer through which the task could otherwise be cancelled.
-/
private theorem shared_uncancelled (matching : PublicationMatching)
    (observed : List Execution.WorkQueueEvent)
    : ¬TaskCancelled work matching observed [(0, firstTask)] sharedTask := by
  rintro ⟨cut, member, _, cause⟩
  have zero : cut = 0 := by simpa using member
  subst cut
  cases cause with
  | owners known _ _ failed =>
      obtain ⟨producer, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique shared_known
      exact child_healthy _ (failed child.key (by simp))
  | producerFailed known _ _ | producerCancelled known _ _ =>
      obtain ⟨owners, payload, known⟩ := known
      cases (known.unique shared_known).2.1

/-- Recording the silent failure after C's notice yields a licensed failure witness.
Witness: the first cut uses open R; the delayed cut uses newly announced C and the
same uncancelled shared task. No queue/source/public-definition change is required.
-/
theorem delayed_cuts_licensed (matching : PublicationMatching)
    : FailureWitness work initial matching events delayedCuts := by
  intro before cut occurrence after split
  cases before with
  | nil =>
      simp only [delayedCuts, List.nil_append, List.cons.injEq, Prod.mk.injEq] at split
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := split
      exact ⟨
        by decide,
        by simp,
        ⟨
          _,
          _,
          _,
          first_known,
          rfl,
          .root ⟨_, _, first_known⟩,
          root.key,
          by simp,
          by decide
        ⟩,
        by simp [TaskCancelled]
      ⟩
  | cons entry rest =>
      cases rest with
      | nil =>
          simp only [delayedCuts, List.cons_append, List.nil_append, List.cons.injEq,
            Prod.mk.injEq] at split
          obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := split
          exact ⟨
            by decide,
            by simp,
            ⟨
              _,
              _,
              _,
              shared_known,
              rfl,
              .root ⟨_, _, shared_known⟩,
              child.key,
              by simp,
              child_failure_open.1
            ⟩,
            shared_uncancelled matching _
          ⟩
      | cons next rest =>
          have lengths := congrArg List.length split
          simp [delayedCuts] at lengths

/-- The actual settlement cut is licensed even though none of its owners is open.
Witness: R's prior announcement and C's continuing health, without moving the cut.
-/
theorem source_cuts_licensed (matching : PublicationMatching)
    : FailureWitness work initial matching events candidateCuts := by
  apply candidate_inventory.failureWitness_iff.mpr
  constructor
  · intro entry member
    simp only [candidateCuts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, ⟨_, _, first_known⟩, root.key, by simp, by decide⟩
    · exact ⟨_, ⟨_, _, shared_known⟩, root.key, by simp, by decide⟩
  · intro before cut occurrence after split
    match before with
    | [] =>
        simp only [candidateCuts, List.nil_append, List.cons.injEq, Prod.mk.injEq] at split
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := split
        simp [TaskCancelled]
    | [entry] =>
        simp only [candidateCuts, List.cons_append, List.nil_append, List.cons.injEq,
          Prod.mk.injEq] at split
        obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := split
        exact shared_uncancelled matching _
    | _ :: _ :: _ =>
        have lengths := congrArg List.length split
        simp [candidateCuts] at lengths

/-- Delaying the silent cut changes no error total at any actual failed-group closure.
Witness: the general first-report inventory theorem retains every contributing occurrence
needed by each closure; no enumeration of the possible event indices is needed.
-/
theorem delayed_exact_counts {index group errors}
    (atEvent : events[index]? = some (.groupFailure group errors))
    : NodeErrors work (failedBefore delayedCuts index) group.key errors :=
  delayed_inventory.2.2.2.1 index group errors atEvent

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerSilentFailureCuts
