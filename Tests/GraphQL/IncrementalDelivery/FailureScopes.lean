import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureAwareSourceCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TerminalReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureReportOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.CausalReportAssembly
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingFailureScopes
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingClosures
import Proofs.GraphQL.IncrementalDelivery.Correctness.ZeroFailureOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.InitialDependencyStability
import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupFailurePositivity
import Proofs.GraphQL.IncrementalDelivery.Correctness.AcceptedFailureReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.UnannouncedGroupFailureOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.RootGroupReportingExistence
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedRefRoles
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedMixedOwners
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Client-visible failure coverage, including a shared latent owner's cancellation.
These checks distinguish observable failure paths from internal task accounting.
-/

namespace GraphQL.IncrementalDelivery.Tests.FailureScopes
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def bubbled : ExecutionObservation :=
  .incremental
    {
      data := .object [("user", .object [("details", .object [])])],
      pending := [{ id := "0", path := [.field "user", .field "details"] }],
      hasNext := true
    }
    [{ hasNext := false, completed := [{ id := "0", errors := 1 }] }]

/-- A descendant failed scope explains an ordinary null ancestor, not just descendants.
Witness: the reference's sole leaf is null user; the notice is at user.details.
-/
example : bubbled.AddressesResponsePositions false (.object [("user", .null)]) := by
  refine ⟨[[]], [[.field "user", .field "details"]], by cbv, by cbv, ?_⟩
  intro path member
  have same : path = [.field "user"] := by simpa [ResponsePositions.value,
    ResponsePositions.fields] using member
  subst path
  exact Or.inr ⟨[.field "user", .field "details"], by simp, Or.inr ⟨rfl, by decide⟩⟩

private def selections : List Selection :=
  [
    field "user" [defer [field "required"] (some "D")],
    defer [field "a", defer [field "user" [field "required"], field "b"] (some "H")]
      (some "P")
  ]

private def completed :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1

private def deep : DeliveryNode :=
  { ref := 2, path := [.field "user"], label := some (.string "D") }

private def parent : DeliveryNode := { ref := 0, path := [], label := some (.string "P") }
private def hidden : DeliveryNode := { ref := 1, path := [], label := some (.string "H") }
private def sharedTask : Occurrence := .executionGroup [0, 0, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 0]
private def hiddenTask : Occurrence := .executionGroup [1, 1, 0]
private def parentData : List (Name × ResponseValue) := [("a", .scalar "a")]
private def hiddenData : List (Name × ResponseValue) := [("b", .scalar "b")]

private def work : Work :=
  .combine
    (.combine
      (.combine .empty
        (.combine
          (.executionGroup [⟨deep, []⟩, ⟨hidden, [parent]⟩] [.field "user"]
            (.error 1) .empty) .empty)) .empty)
    (.combine
      (.executionGroup [⟨parent, []⟩] [] (.ok (parentData, 0)) (.combine .empty .empty))
      (.combine
        (.executionGroup [⟨hidden, [parent]⟩] [] (.ok (hiddenData, 0))
          (.combine .empty .empty)) .empty))

/-- The problematic shared and private tasks are produced by real query execution.
Witness: reduction of defer collection and pure field completion.
-/
theorem execution_generated : completed.work = work := by cbv

private theorem shared_known
    : TaskAt work sharedTask [deep.ref, hidden.ref] none
        (.object [.field "user"] (.error 1)) :=
  ⟨_, _, _, _, [], rfl, rfl, rfl⟩

private theorem parent_known
    : TaskAt work parentTask [parent.ref] none (.object [] (.ok (parentData, 0))) :=
  ⟨_, _, _, _, [], rfl, rfl, rfl⟩

private theorem hidden_known
    : TaskAt work hiddenTask [hidden.ref] none (.object [] (.ok (hiddenData, 0))) :=
  ⟨_, _, _, _, [], rfl, rfl, rfl⟩

private theorem task_cases {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = sharedTask ∨ occurrence = parentTask ∨ occurrence = hiddenTask := by
  have member := known.observationToken
  simpa [observationTokens, work, sharedTask, parentTask, hiddenTask] using member

private theorem node_cases {node kind dependencies producer}
    (known : NodeAt work node kind dependencies producer)
    : kind = .group
      ∧ producer = none
      ∧ ((node = deep ∧ dependencies = [])
          ∨ (node = hidden ∧ dependencies = [parent.ref])
          ∨ (node = parent ∧ dependencies = [])) := by
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have group : kind = .group := by
    have role := Correctness.node_ref_role roles known
    cases kind with
    | group => rfl
    | stream => change false = true at role; cases role
  subst kind
  obtain ⟨address, groups, path, result, children, enclosing, selected,
    located, member, rfl, rfl⟩ := known
  have task : TaskAt work (.executionGroup address)
      (groups.map (fun group => group.node.ref)) producer (.object path result) :=
    ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩
  rcases task_cases task with same | same | same
  · have equalAddress := Occurrence.executionGroup.inj same
    change address = [0, 0, 1, 0] at equalAddress
    subst address
    have equal : groups = [⟨deep, []⟩, ⟨hidden, [parent]⟩] ∧ producer = none := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact ⟨equal.1.1, equal.2.1⟩
    rcases equal with ⟨rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp
  · have equalAddress := Occurrence.executionGroup.inj same
    change address = [1, 0] at equalAddress
    subst address
    have equal : groups = [⟨parent, []⟩] ∧ producer = none := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact ⟨equal.1.1, equal.2.1⟩
    rcases equal with ⟨rfl, rfl⟩
    obtain rfl := List.mem_singleton.mp member
    simp
  · have equalAddress := Occurrence.executionGroup.inj same
    change address = [1, 1, 0] at equalAddress
    subst address
    have equal : groups = [⟨hidden, [parent]⟩] ∧ producer = none := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact ⟨equal.1.1, equal.2.1⟩
    rcases equal with ⟨rfl, rfl⟩
    obtain rfl := List.mem_singleton.mp member
    simp

private theorem deep_node : NodeAt work deep .group [] none :=
  ⟨[0, 0, 1, 0], _, _, _, _, [], ⟨deep, []⟩, rfl, by simp, rfl, rfl⟩

private theorem parent_node : NodeAt work parent .group [] none :=
  ⟨[1, 0], _, _, _, _, [], ⟨parent, []⟩, rfl, by simp, rfl, rfl⟩

private theorem hidden_node : NodeAt work hidden .group [parent.ref] none :=
  ⟨[0, 0, 1, 0], _, _, _, _, [], ⟨hidden, [parent]⟩, rfl, by simp, rfl, rfl⟩

private def matching : PublicationMatching := fun _ => parentTask
private def failures : FailureCuts := [(0, sharedTask)]
private def initial : NodeRefs := [deep.ref, parent.ref]

private def values : WorkQueueEvent :=
  .groupValues parent [{ path := [], data := parentData, deliveryGroups := [parent] }]

private def events : List WorkQueueEvent :=
  [.groupFailure deep 1, values, .groupSuccess parent [] []]

private theorem parent_healthy (observed : List WorkQueueEvent)
    : ¬NodeFailed work matching observed failures parent.ref := by
  rintro ⟨cut, member, _, cause⟩
  have zero : cut = 0 := by simpa [failures] using member
  subst cut
  change Causality.NodeFailed work [sharedTask] _ parent.ref at cause
  cases cause with
  | task known owner recorded =>
      obtain rfl := List.mem_singleton.mp recorded
      obtain ⟨birth, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique shared_known
      simp [deep, parent, hidden] at owner
  | groupDependency known member _ =>
      obtain ⟨node, birth, known, same⟩ := known
      rcases (node_cases known).2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp_all [deep, parent, hidden]
  | streamDependencies known _ _ =>
      obtain ⟨node, birth, known, _⟩ := known
      cases (node_cases known).1
  | producers _ noRoot _ _ => exact noRoot ⟨parent, .group, [], parent_node, rfl⟩

private theorem parent_uncancelled (observed : List WorkQueueEvent)
    : ¬TaskCancelled work matching observed failures parentTask := by
  rintro ⟨cut, member, bound, cause⟩
  have zero : cut = 0 := by simpa [failures] using member
  subst cut
  cases cause with
  | owners known _ _ failed =>
      obtain ⟨birth, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique parent_known
      exact parent_healthy observed ⟨0, member, bound, failed parent.ref (by simp)⟩
  | producerFailed known _ _ | producerCancelled known _ _ =>
      obtain ⟨owners, payload, known⟩ := known
      cases (known.unique parent_known).2.1

private theorem initial_eligible {node occurrence owners payload}
    (known : TaskAt work occurrence owners none payload) (owner : node.ref ∈ owners)
    : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
  refine ⟨
    by simp [announcedRefs, pendingRefs],
    Or.inl ⟨by simp [NodeFailed], Or.inr ?_⟩,
    by simp,
    by simp
  ⟩
  intro accounted
  rcases accounted occurrence owners ⟨_, _, known⟩ owner with cancelled | published
  · simp [TaskCancelled] at cancelled
  · simp [Published] at published

private theorem initialized : Initializes work [deep, parent] [] := by
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨[], none, deep_node, initial_eligible shared_known (by simp)⟩
  · exact ⟨[], none, parent_node, initial_eligible parent_known (by simp)⟩

private theorem failure_licensed
    : FailureWitness work initial matching events failures := by
  intro before cut occurrence after equal
  have sizes := congrArg List.length equal
  simp only [failures, List.length_append, List.length_cons, List.length_nil] at sizes
  have emptyBefore : before = [] := List.eq_nil_of_length_eq_zero (by omega)
  have emptyAfter : after = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst before
  subst after
  have same : (0, sharedTask) = (cut, occurrence) := by simpa [failures] using equal
  cases same
  refine ⟨by decide, by simp, ?_, by simp [TaskCancelled]⟩
  exact ⟨
    _,
    _,
    _,
    shared_known,
    rfl,
    .root ⟨_, _, shared_known⟩,
    deep.ref,
    by simp,
    by decide
  ⟩

private theorem failure_allowed
    : EventAllowed work initial matching [] failures (.groupFailure deep 1) := by
  refine ⟨⟨[], none, deep_node⟩, by unfold Open; decide, ?_, ?_⟩
  · exact NodeFailed.task shared_known (by simp) (by simp [failures, failedBefore])
  · refine ⟨fun _ => 1, ?_, rfl⟩
    intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, _, _, shared_known, by simp [Payload.failure]⟩

private theorem values_allowed
    : EventAllowed work initial matching [.groupFailure deep 1] failures values := by
  refine ⟨[parent.ref], none,
    { path := [], data := parentData, deliveryGroups := [parent] },
    rfl, parent_known, ?_, ?_⟩
  · refine ⟨?_, parent_uncancelled _, by simp, trivial⟩
    rintro ⟨index, event, selected, value, _⟩
    cases index with
    | zero => cases selected; exact value
    | succ index => simp at selected
  · have opened : OpenOwner work initial [.groupFailure deep 1] [parent.ref] parent :=
      ⟨⟨.group, [], none, parent_node⟩, by simp, by unfold Open; decide⟩
    refine ⟨opened, ⟨parent, opened, parent_healthy _⟩, ?_⟩
    intro other available
    obtain ⟨kind, dependencies, producer, known⟩ := available.1
    rcases (node_cases known).2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · have owner := available.2.1
      simp [deep, parent] at owner
    · have owner := available.2.1
      simp [hidden, parent] at owner
    · exact Nat.le_refl _

private theorem parent_published
    : Published matching [.groupFailure deep 1, values] parentTask :=
  ⟨1, values, rfl, trivial, rfl⟩

private theorem closure_allowed
    : EventAllowed work initial matching [.groupFailure deep 1, values] failures
        (.groupSuccess parent [] []) := by
  refine ⟨⟨[], none, parent_node⟩, by unfold Open; decide, parent_healthy _, ?_, ?_⟩
  · rintro occurrence owners ⟨birth, payload, known⟩ owner
    rcases task_cases known with rfl | rfl | rfl
    · obtain ⟨rfl, _, _⟩ := known.unique shared_known
      simp [deep, parent, hidden] at owner
    · exact Or.inr parent_published
    · obtain ⟨rfl, _, _⟩ := known.unique hidden_known
      simp [parent, hidden] at owner
  · exact ⟨by simp, by simp, by simp⟩

private theorem explained : Explains work [deep, parent] [] events matching failures := by
  refine ⟨initialized, failure_licensed, ?_⟩
  intro index event selected
  match index with
  | 0 => cases selected; exact failure_allowed
  | 1 => cases selected; exact values_allowed
  | 2 => cases selected; exact closure_allowed
  | index + 3 => simp [events] at selected

/-- The omitted b task is internally accounted for by causal cancellation.
Witness: D's shared failure also fails H, whose private task is unpublished.
This weaker property does not supply an observable scope covering b.
-/
theorem internally_accounted
    : ∀ occurrence owners producer payload,
        TaskAt work occurrence owners producer payload
        → TaskAccounted work matching events failures occurrence := by
  intro occurrence owners producer payload known
  rcases task_cases known with rfl | rfl | rfl
  · apply Or.inl
    refine ⟨0, by simp [failures], by simp, ?_⟩
    apply Causality.TaskCancelled.owners ⟨_, _, shared_known⟩
      (by simp [Published, events, values]) (by simp)
    intro ref member
    exact Causality.NodeFailed.task ⟨_, _, shared_known⟩ member
      (by simp [failedBefore, failures])
  · exact Or.inr (parent_published.append _)
  · apply Or.inl
    refine ⟨0, by simp [failures], by simp, ?_⟩
    apply Causality.TaskCancelled.owners ⟨_, _, hidden_known⟩
      (by simp [Published, events, values]) (by simp)
    intro ref member
    obtain rfl := List.mem_singleton.mp member
    exact Causality.NodeFailed.task ⟨_, _, shared_known⟩ (by simp)
      (by simp [failedBefore, failures])

/-- The incomplete prefix may omit H while its private b remains undelivered.
Witness: unchanged event admission permits D's failure and P's publication/closure;
the prefix makes no promise that client-visible reporting is complete.
-/
theorem hidden_cancellation_prefix_admitted
    : AdmissiblePrefix work ⟨[deep, parent], [], [events]⟩ := by
  refine ⟨events, matching, failures, explained, ?_⟩
  exact .cons (batch := events) (by simp [events])
    (.separate _ (.separate _ (.separate _ .nil))) .nil

/-- Internal cancellation accounting cannot justify premature termination without H.
Witness: the unpublished b task needs a report covering its root attachment path;
D's sole failure completion at user cannot supply one, regardless of failure cuts.
-/
theorem hidden_cancellation_not_terminal (anyFailures : FailureCuts)
    : ¬Terminal work initial matching events anyFailures := by
  intro terminal
  have addressed := terminal.1 hiddenTask [hidden.ref] none
    (.object [] (.ok (hiddenData, 0))) hidden_known
  rcases addressed with ⟨_, node, errors, positive, below, failure⟩ | published
  · rcases failure with member | member
    · have same : node = deep ∧ errors = 1 := by simpa [events, values] using member
      rcases same with ⟨rfl, _⟩
      exact (by decide : ¬deep.path.IsPrefix []) below
    · simp [events, values] at member
  · simp [Published, matching, parentTask, hiddenTask] at published

/-- Covering only healthy supported notices does not cover retained failed-owner notices.
Witness: D and P are already announced, while H is failed by the accepted shared task.
Thus the old proof-construction invariant holds even at this reporting-incomplete prefix.
-/
theorem hidden_cancellation_supported_notices_covered
    (ancestry : Semantics.Ancestry.Assignment)
    : Correctness.SupportedNoticesCovered ancestry work initial matching events
        failures := by
  intro node kind dependencies producer known supported
  rcases (node_cases known).2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact supported.1.1 (by decide)
  · exact supported.2.1 (NodeFailed.task shared_known (by simp)
      (by simp [failedBefore, failures]))
  · exact supported.1.1 (by decide)

/-- The failed broader owner remains eligible for a notice after the parent closes.
Witness: H's retained shared failure and P's completed dependency satisfy CanAnnounce.
Eligibility alone is not an output event and does not create a notice carrier.
-/
theorem hidden_cancellation_notice_eligible
    : CanAnnounce work initial matching events failures hidden .group [parent.ref]
        none := by
  refine ⟨by decide, Or.inr ?_, by simp, ?_⟩
  · exact ⟨rfl, sharedTask, [deep.ref, hidden.ref], by simp [failedBefore, failures],
      ⟨_, _, shared_known⟩, by simp⟩
  · intro ref member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨parent_healthy _, Or.inr (Or.inl (by decide))⟩

/-- Reporting-aware construction excludes the stranded prefix admitted by healthy cover.
Witness: the still-eligible failed H notice contradicts its all-group component, without
assuming termination or any observable report for the private b attachment.
-/
theorem hidden_cancellation_not_reporting_covered
    (ancestry : Semantics.Ancestry.Assignment)
    : ¬Correctness.ReportingNoticesCovered ancestry work initial matching events
        failures := by
  intro covered
  exact covered.2 hidden [parent.ref] none hidden_node hidden_cancellation_notice_eligible

/-- No admitted next event at this prefix can carry the missing notice.
Witness: all announced refs are already closed, excluding group-success carriers; this
generated work has no stream tasks, excluding stream-value carriers. The assertion holds
for any next matching and failure evidence, not only the prefix's selected witnesses.
-/
theorem hidden_cancellation_no_notice_carrier
    (next : PublicationMatching) (cuts : FailureCuts) (event : WorkQueueEvent)
    (allowed : EventAllowed work initial next events cuts event)
    : eventPending event = [] := by
  cases event <;> try rfl
  case groupSuccess node groups streams =>
    have opened := allowed.2.1
    have closed : (announcedRefs initial events).Subset (completedRefs events) := by
      intro ref
      change ref ∈ [deep.ref, parent.ref] → ref ∈ [deep.ref, parent.ref]
      exact id
    exact False.elim (opened.2 (closed opened.1))
  case streamValues node values groups streams =>
    obtain ⟨owners, producer, value, _, known, _⟩ := allowed
    generalize selected : next events.length = occurrence at known
    cases StructuralEquivalence.taskAt_of_current known with
    | item located entry =>
        rcases task_cases known with impossible | impossible | impossible <;>
          cases impossible

private def reportedEvents : List WorkQueueEvent :=
  [.groupFailure deep 1, values, .groupSuccess parent [hidden] [], .groupFailure hidden 1]

/-- The parent's success can release the latent failed co-owner after shared settlement.
Witness: its recorded contributing failure licenses the notice once P's dependency closes.
The ordinary healthy-notice alternative is neither available nor assumed for H.
-/
private theorem reporting_release_allowed
    : EventAllowed work initial matching [.groupFailure deep 1, values] failures
        (.groupSuccess parent [hidden] []) := by
  refine ⟨closure_allowed.1, closure_allowed.2.1, closure_allowed.2.2.1,
    closure_allowed.2.2.2.1, ?_⟩
  refine ⟨by decide, ?_, by simp⟩
  intro node member
  obtain rfl := List.mem_singleton.mp member
  refine ⟨[parent.ref], none, hidden_node, by decide, Or.inr ?_, by simp, ?_⟩
  · exact ⟨rfl, sharedTask, [deep.ref, hidden.ref], by simp [failedBefore, failures],
      ⟨_, _, shared_known⟩, by simp⟩
  · intro ref member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨parent_healthy _, Or.inr (Or.inl (by decide))⟩

/-- Releasing H then emitting its counted failure is admitted without a terminal premise.
Witness: retain the earlier failed shared task and parent's publication, announce H through
the success carrier, then close its open ref with the shared task's one counted error.
-/
private theorem reporting_explained
    : Explains work [deep, parent] [] reportedEvents matching failures := by
  have head : Explains work [deep, parent] [] [.groupFailure deep 1, values]
      matching failures := by
    have shorter := explained.prefix (head := [.groupFailure deep 1, values])
      (tail := [.groupSuccess parent [] []])
    simpa [failures] using shorter
  have released := head.append_event reporting_release_allowed
  apply released.append_event
  refine ⟨⟨[parent.ref], none, hidden_node⟩, by unfold Open; decide, ?_, ?_⟩
  · exact NodeFailed.task shared_known (by simp) (by simp [failedBefore, failures])
  · refine ⟨fun _ => 1, ?_, rfl⟩
    intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, _, _, shared_known, by simp [Payload.failure]⟩

/-- Releasing the retained owner repairs the stronger constructive frontier.
Witness: every represented group is announced in the repaired history, so none is fresh.
No terminal law or failure-report premise is used to establish this coverage invariant.
-/
theorem late_owner_reporting_covered (ancestry : Semantics.Ancestry.Assignment)
    : Correctness.ReportingNoticesCovered ancestry work initial matching reportedEvents
        failures := by
  apply Correctness.reportingNoticesCovered_of_noticesCovered
  intro node kind dependencies producer known notice
  rcases (node_cases known).2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
    exact notice.1 (by decide)

/-- Generated shared-owner work admits accounting and closure with its frontier retained.
Witness: execution supplies ref roles, ancestry, continuity, stream order, and owner paths;
the stronger maximal extension starts from covering initial notices. This does not assume
the reporting-incomplete fixture's terminal continuation or a complete response outcome.
-/
theorem generated_reporting_accounting
    : ∃ ancestry groups streams observed next cuts,
        Explains work groups streams observed next cuts
        ∧ Correctness.ReportingNoticesCovered ancestry work
            ((groups ++ streams).map DeliveryNode.ref) next observed cuts
        ∧ (∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload
            → TaskAccounted work next observed cuts occurrence)
        ∧ ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) observed,
            ref ∈ completedRefs observed := by
  obtain ⟨_, ancestry, valid, coherent, continuous⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  obtain ⟨roles, roleCoherent⟩ := Semantics.RefRoles.executeRoot_roles schema resolvers [] 30
    "Query" (.object "Query" 0) selections 0
  obtain ⟨paths, pathCoherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  have ordered := Semantics.GeneralScheduling.executeRoot_streamOwnersOrdered schema
    resolvers [] 30 "Query" (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  change Semantics.GeneralScheduling.DeferContinuous ancestry completed.work at continuous
  change Semantics.RefRoles.WorkRoles roles completed.work at roleCoherent
  change Semantics.MixedOwnerPaths.WorkAt paths _ completed.work at pathCoherent
  change Semantics.GeneralScheduling.StreamOwnersOrdered completed.work at ordered
  rw [execution_generated] at coherent continuous roleCoherent pathCoherent ordered
  obtain ⟨groups, streams, starts, covers⟩ := initialized.covering_exists
  have first : Explains work groups streams [] matching [] :=
    ⟨starts, by simp [FailureWitness], by simp⟩
  obtain ⟨tail, next, cuts, admitted, frontier, accounted, closed, _⟩ :=
    Correctness.mixed_reporting_closed_extension valid coherent roleCoherent continuous
      ordered pathCoherent first
      (Correctness.reportingNoticesCovered_of_noticesCovered
        (NoticesCovered.initial covers matching))
  exact ⟨
    ancestry,
    groups,
    streams,
    tail,
    next,
    cuts,
    by simpa using admitted,
    by simpa using frontier,
    by simpa using accounted,
    by simpa using closed
  ⟩

/-- The generated latent shared-owner fixture has a complete, actually reported run.
Witness: root-descriptor finite existence constructs notices, accounting, scopes, and
termination together. H has a real defer dependency, so this is not an all-root-notice
or empty-dependency special case, nor does it assume the desired terminal history.
-/
theorem generated_reporting_completeRun : ∃ history, AdmissibleRun work history := by
  obtain ⟨_, ancestry, valid, coherent, continuous⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  obtain ⟨paths, pathCoherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  have ordered := Semantics.GeneralScheduling.executeRoot_streamOwnersOrdered schema
    resolvers [] 30 "Query" (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  change Semantics.GeneralScheduling.DeferContinuous ancestry completed.work at continuous
  change Semantics.MixedOwnerPaths.WorkAt paths _ completed.work at pathCoherent
  change Semantics.GeneralScheduling.StreamOwnersOrdered completed.work at ordered
  rw [execution_generated] at coherent continuous pathCoherent ordered
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have positive : Correctness.ExecutionErrors.WorkPositive work := by
    simp [Correctness.ExecutionErrors.WorkPositive, Semantics.BasicErrors.PositiveFailure,
      work]
  have under : Correctness.ExecutionPaths.WorkUnder [] work := by
    simp [Correctness.ExecutionPaths.WorkUnder, work]
  exact Correctness.completeRun_exists_of_root_group_descriptors valid coherent roles
    continuous ordered pathCoherent under positive
    (fun _ _ _ known => (node_cases known).2.1) (by decide)

/-- No explanation can give this generated root group a zero-count failure completion.
Witness: the general zero-count origin theorem needs a failed dependency or unavailable
producer, but this root descriptor has neither. Counted errors on success are unaffected.
-/
theorem root_zero_failure_unexplained (outputs : List WorkQueueEvent)
    (next : PublicationMatching) (cuts : FailureCuts) (index : Nat)
    (selected : outputs[index]? = some (.groupFailure deep 0))
    : ¬Explains work [deep, parent] [] outputs next cuts := by
  intro explained
  obtain ⟨_, ancestry, _, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  rw [execution_generated] at coherent
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have positive : Correctness.ExecutionErrors.WorkPositive work := by
    simp [Correctness.ExecutionErrors.WorkPositive, Semantics.BasicErrors.PositiveFailure,
      work]
  rcases Correctness.Explains.zero_group_completion_dependency_or_unavailable_producer
    coherent roles positive explained deep_node selected with dependency | producer
  · obtain ⟨ref, impossible, _⟩ := dependency
    cases impossible
  · obtain ⟨source, impossible, _⟩ := producer
    cases impossible

/-- The healthy accounted parent cannot acquire a recorded contributor failure later.
Witness: the generic settlement/accounting boundary, with P's actual publication and
healthy ref. Shared failures for D and H are not incorrectly charged to P.
-/
theorem healthy_parent_has_no_recorded_failure
    : ¬HasRecordedFailure work failures reportedEvents.length parent.ref := by
  apply reporting_explained.healthy_accounted_no_recorded_failure
    (index := reportedEvents.length)
  · simpa only [List.take_length] using parent_healthy reportedEvents
  · rw [List.take_length]
    rintro occurrence owners ⟨producer, payload, known⟩ member
    rcases task_cases known with rfl | rfl | rfl
    · obtain ⟨rfl, _, _⟩ := known.unique shared_known
      simp [deep, hidden, parent] at member
    · exact Or.inr ⟨1, values, rfl, trivial, rfl⟩
    · obtain ⟨rfl, _, _⟩ := known.unique hidden_known
      simp [hidden, parent] at member

/-- The satisfied parent remains healthy when its retained child's failure closes later.
Witness: full-ancestry stability on the shared admitted history, starting at P's success
closure. The chosen failure cuts and publication matching are unchanged throughout.
-/
theorem satisfied_parent_stays_healthy
    : ¬NodeFailed work matching reportedEvents failures parent.ref := by
  obtain ⟨_, ancestry, valid, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  rw [execution_generated] at coherent
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have empty : ancestry parent.ref = [] :=
    (Correctness.DeferOnly.node_dependencies coherent parent_node).symm
  apply Correctness.Explains.supported_defer_dependency_stays_healthy (index := 3)
    valid coherent roles reporting_explained rfl
    ⟨parent_healthy _, Or.inr (Or.inl (by decide))⟩
  intro ref member
  simp [empty] at member

/-- The retained hidden-group notice supplies lasting health of its parent dependency.
Witness: invert the actual group-success carrier rather than separately assuming its
dependency support. The later hidden-group failure cannot invalidate that support.
-/
theorem retained_notice_dependencies_stay_healthy
    : ∀ ref ∈ [parent.ref], ¬NodeFailed work matching reportedEvents failures ref := by
  obtain ⟨_, ancestry, valid, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  rw [execution_generated] at coherent
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  exact Correctness.Explains.carried_group_notice_dependencies_stay_healthy (index := 2)
    (event := .groupSuccess parent [hidden] []) valid coherent roles reporting_explained
    rfl hidden_node (by decide)

/-- The general announced-group theorem covers the retained shared owner as well.
Witness: execution-derived ancestry and the actual final notice history; neither initial
nor later notices are assumed to have separately stable dependencies.
-/
theorem announced_hidden_dependencies_stay_healthy
    : ∀ ref ∈ [parent.ref], ¬NodeFailed work matching reportedEvents failures ref := by
  obtain ⟨_, ancestry, valid, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  rw [execution_generated] at coherent
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  exact Correctness.Explains.announced_group_dependencies_stay_healthy valid coherent
    roles reporting_explained hidden_node (by decide)

/-- Zero-count group failure is excluded at every admitted output position, not only roots.
Witness: the general positivity theorem with execution-derived full ancestry and positive
failed payloads. Matching, cuts, descriptor, and output position are arbitrary.
-/
theorem zero_group_failure_unexplained
    {observed next cuts node} {index : Nat}
    (selected : observed[index]? = some (.groupFailure node 0))
    : ¬Explains work [deep, parent] [] observed next cuts := by
  intro admitted
  obtain ⟨_, ancestry, valid, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  rw [execution_generated] at coherent
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have positive : Correctness.ExecutionErrors.WorkPositive work := by
    simp [Correctness.ExecutionErrors.WorkPositive, Semantics.BasicErrors.PositiveFailure,
      work]
  have nonzero := Correctness.Explains.group_failure_positive valid coherent roles positive
    admitted selected
  omega

/-- Actual notice and failure evidence reports the retained owner's complete root scope.
Witness: generated-work group scope reporting; ID closure and actual failure suffice,
without separately promising an eventual contributor notice or the desired scope.
-/
theorem announced_failed_hidden_reports_scope
    : FailureReportedFor reportedEvents hidden.path := by
  obtain ⟨_, ancestry, valid, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  obtain ⟨paths, pathCoherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  change Semantics.MixedOwnerPaths.WorkAt paths _ completed.work at pathCoherent
  rw [execution_generated] at coherent pathCoherent
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have positive : Correctness.ExecutionErrors.WorkPositive work := by
    simp [Correctness.ExecutionErrors.WorkPositive, Semantics.BasicErrors.PositiveFailure,
      work]
  apply Correctness.Explains.announced_failed_group_reports_scope valid coherent roles
    pathCoherent positive reporting_explained
  · intro ref member
    exact member
  · exact hidden_node
  · decide
  · exact NodeFailed.task shared_known (by simp) (by simp [failedBefore, failures])

/-- Every accepted failure in this generated work has an actual attachment report.
Witness: the generic acceptance-origin theorem for arbitrary admitted output histories and
cuts, with all announced IDs closed. No future co-owner announcement is supplied.
-/
theorem every_accepted_failure_reported
    {observed next cuts cut occurrence owners birth payload}
    (admitted : Explains work [deep, parent] [] observed next cuts)
    (closed : ∀ ref ∈ announcedRefs initial observed, ref ∈ completedRefs observed)
    (recorded : (cut, occurrence) ∈ cuts)
    (known : TaskAt work occurrence owners birth payload)
    : FailureReportedFor observed payload.path := by
  obtain ⟨_, ancestry, valid, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  obtain ⟨paths, pathCoherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  change Semantics.MixedOwnerPaths.WorkAt paths _ completed.work at pathCoherent
  rw [execution_generated] at coherent pathCoherent
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have positive : Correctness.ExecutionErrors.WorkPositive work := by
    simp [Correctness.ExecutionErrors.WorkPositive, Semantics.BasicErrors.PositiveFailure,
      work]
  exact Correctness.Explains.accepted_failure_reported valid coherent roles pathCoherent
    positive admitted closed recorded known

/-- A failed latent root group covers its private task in any closed reporting frontier.
Witness: task-local ancestor descent with execution-derived metadata. This quantifies over
admitted histories without separately requiring that H, or every group, was announced.
-/
theorem latent_failed_owner_reports_private_task
    {observed next cuts}
    (admitted : Explains work [deep, parent] [] observed next cuts)
    (covered : Correctness.GroupNoticesCovered work initial next observed cuts)
    (satisfied
      : ∀ ref,
          ¬NodeFailed work next observed cuts ref
          → DependencySatisfied work initial next observed cuts ref)
    (closed : ∀ ref ∈ announcedRefs initial observed, ref ∈ completedRefs observed)
    (failed : NodeFailed work next observed cuts hidden.ref)
    : FailureReportedFor observed ([] : ResponsePath) := by
  obtain ⟨_, ancestry, valid, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  obtain ⟨paths, pathCoherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  change Semantics.MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  change Semantics.MixedOwnerPaths.WorkAt paths _ completed.work at pathCoherent
  rw [execution_generated] at coherent pathCoherent
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have positive : Correctness.ExecutionErrors.WorkPositive work := by
    simp [Correctness.ExecutionErrors.WorkPositive, Semantics.BasicErrors.PositiveFailure,
      work]
  exact Correctness.Explains.failed_owner_reported_of_root_groups valid coherent roles
    pathCoherent positive admitted covered satisfied closed
    (fun _ _ _ known => (node_cases known).2.1) hidden_known hidden_node (by simp) failed

/-- A late co-owner notice reports the broader private attachment lost to shared failure.
Witness: the eventual-contributor theorem applied to the admitted repaired history; its
root scope covers b even though the failed shared task itself is attached only at user.
No terminal law or previously supplied covering report is used.
-/
theorem late_owner_reports_private_attachment
    : FailureReportedFor reportedEvents
        (Payload.object [] (.ok (hiddenData, 0))).path := by
  obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  change Semantics.MixedOwnerPaths.WorkAt paths _ completed.work at coherent
  rw [execution_generated] at coherent
  exact Correctness.Explains.recorded_owner_reported_of_eventual_notice
    (cut := 0)
    coherent reporting_explained
    (by
      intro ref
      change ref ∈ [deep.ref, parent.ref, hidden.ref]
        → ref ∈ [deep.ref, parent.ref, hidden.ref]
      exact id)
    (by simp [failures])
    shared_known
    (by decide)
    hidden_node
    (by simp)
    (by decide)
    (by decide)

#print axioms late_owner_reports_private_attachment
#print axioms Correctness.Explains.recorded_task_reported_of_surviving_notices

/-- The reporting frontier derives H's broad observable scope without a notice premise.
Witness: satisfied P dependency, retained shared settlement, generated positive failures,
and actual closure. The supplied frontier is constructive coverage, not Terminal.
-/
theorem retained_frontier_reports_private_attachment
    : FailureReportedFor reportedEvents
        (Payload.object [] (.ok (hiddenData, 0))).path := by
  obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  change Semantics.MixedOwnerPaths.WorkAt paths _ completed.work at coherent
  rw [execution_generated] at coherent
  have positive : Correctness.ExecutionErrors.WorkPositive work := by
    simp [Correctness.ExecutionErrors.WorkPositive, Semantics.BasicErrors.PositiveFailure,
      work]
  apply Correctness.Explains.recorded_group_reported_of_covered_frontier
    (cut := 0)
    coherent positive reporting_explained (late_owner_reporting_covered (fun _ => [])).2
    (by
      intro ref
      change ref ∈ [deep.ref, parent.ref, hidden.ref]
        → ref ∈ [deep.ref, parent.ref, hidden.ref]
      exact id)
    (by simp [failures])
    shared_known hidden_node
    (by simp)
    (by decide)
    (by simp)
  intro ref member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨parent_healthy _, Or.inr (Or.inl (by decide))⟩

/-- The causal assembly theorem recovers the cancelled private task's actual broad scope.
Witness: concrete failed group notices and accepted shared settlement, followed by the
owner-cancellation rule. The parent's successful publication cannot serve as a report.
-/
theorem late_scope_assembles_private_report
    : FailureReportedFor reportedEvents
        (.object [] (.ok (hiddenData, 0)) : Payload).path := by
  obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  change Semantics.MixedOwnerPaths.WorkAt paths _ completed.work at coherent
  rw [execution_generated] at coherent
  have under : Correctness.ExecutionPaths.WorkUnder [] work := by
    simp [Correctness.ExecutionPaths.WorkUnder, work]
  have cancelled : TaskCancelled work matching reportedEvents failures hiddenTask := by
    refine ⟨0, by simp [failures], by simp, ?_⟩
    apply Causality.TaskCancelled.owners ⟨_, _, hidden_known⟩
      (by simp [Published]) (by simp)
    intro ref member
    obtain rfl := List.mem_singleton.mp member
    exact Causality.NodeFailed.task ⟨_, _, shared_known⟩ (by simp)
      (by simp [failedBefore, failures])
  apply Correctness.cancelled_reported_of_group_and_task_scopes coherent under ?_ ?_
    cancelled hidden_known
  · intro node dependencies birth known failed
    rcases (node_cases known).2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨deep, 1, by decide, ⟨[], by simp⟩, Or.inl (by simp [reportedEvents])⟩
    · exact late_owner_reports_private_attachment
    · exact False.elim (parent_healthy _ failed)
  · intro cut occurrence member owners producer payload known
    have same : cut = 0 ∧ occurrence = sharedTask := by simpa [failures] using member
    rcases same with ⟨rfl, rfl⟩
    have scope : FailureReportedFor reportedEvents [.field "user"] :=
      late_owner_reports_private_attachment.descendant ⟨[.field "user"], rfl⟩
    exact (shared_known.unique known).2.2 ▸ scope

#print axioms Correctness.snapshot_cancelled_reported_of_group_and_task_scopes
#print axioms Correctness.finish_accounted_of_report_scopes
#print axioms late_scope_assembles_private_report
#print axioms hidden_cancellation_supported_notices_covered
#print axioms hidden_cancellation_no_notice_carrier
#print axioms hidden_cancellation_not_reporting_covered
#print axioms late_owner_reporting_covered
#print axioms Correctness.reporting_failure
#print axioms Correctness.reporting_complete_stream
#print axioms Correctness.extend_ready_reporting
#print axioms generated_reporting_accounting
#print axioms Correctness.mixed_reporting_accounted_extension
#print axioms retained_frontier_reports_private_attachment
#print axioms Correctness.Explains.recorded_group_reported_of_covered_frontier
#print axioms Correctness.mixed_reporting_closed_extension
#print axioms root_zero_failure_unexplained
#print axioms Explains.contributor_closed_before_settlement_failed
#print axioms Correctness.Explains.zero_group_completion_no_recorded_failure
#print axioms healthy_parent_has_no_recorded_failure
#print axioms Explains.recorded_task_unaccounted_before_cut
#print axioms Explains.healthy_accounted_no_recorded_failure
#print axioms satisfied_parent_stays_healthy
#print axioms Correctness.Explains.healthy_group_accounted_producer_available
#print axioms Correctness.Explains.supported_defer_dependency_stays_healthy
#print axioms retained_notice_dependencies_stay_healthy
#print axioms Explains.after_carrier_before_settlements
#print axioms Explains.healthy_accounted_no_recorded_failure_before_next_settlements
#print axioms Correctness.Explains.carried_group_notice_dependencies_stay_healthy
#print axioms announced_hidden_dependencies_stay_healthy
#print axioms Correctness.Explains.announced_group_dependencies_stay_healthy
#print axioms Correctness.Initializes.initial_group_dependencies_absent
#print axioms zero_group_failure_unexplained
#print axioms announced_failed_hidden_reports_scope
#print axioms Correctness.Explains.group_failure_positive
#print axioms Correctness.Explains.closed_group_contributor_reports_scope
#print axioms Correctness.Explains.announced_failed_group_reports_scope
#print axioms every_accepted_failure_reported
#print axioms Correctness.Explains.accepted_failure_reported
#print axioms latent_failed_owner_reports_private_task
#print axioms Correctness.Explains.unannounced_group_failure_origin
#print axioms Correctness.Explains.failed_owner_reported_or_unavailable_ancestor
#print axioms generated_reporting_completeRun
#print axioms Correctness.snapshot_cancelled_reported_of_owner_task_scopes
#print axioms Correctness.completeRun_exists_of_root_group_descriptors

private def response : Response := { data := .object [("user", .object [])] }

private def result : ExecutionObservation :=
  Correctness.replayResponse response [deep, parent] []
    [[events ++ [.workQueueTermination]]]

private def operation : Operation := { selectionSet := selections }

private def reference : ResponseValue :=
  .object [("user", .null), ("a", .scalar "a"), ("b", .scalar "b")]

/-- Erasing incremental directives retains b in the ordinary response despite user null.
Witness: pure query execution and non-null bubbling reduction.
-/
theorem reference_eq
    : (GraphQL.Execution.executeQueryWithFuel schema resolvers []
        operation.eraseIncrementalDirectives 30 (.object "Query" 0)).data
      = reference := by
  cbv

/-- The wire observation contains no scope covering the cancelled private b selection.
Witness: the only error completion is D at user; b is neither delivered nor null.
-/
theorem hidden_cancellation_not_addressed
    : ¬result.AddressesResponsePositions false reference := by
  have decoded : result.decodeSlices false = some [[], [[.field "a"]]] := by cbv
  have failed : result.collectFailureScopes = some [[.field "user"]] := by cbv
  rintro ⟨slices, scopes, delivered, failures, covered⟩
  have sameSlices := Option.some.inj (decoded.symm.trans delivered)
  have sameScopes := Option.some.inj (failed.symm.trans failures)
  subst slices
  subst scopes
  have missing := covered [.field "b"] (by decide)
  rcases missing with delivered | ⟨scope, member, below⟩
  · simp at delivered
  · obtain rfl := List.mem_singleton.mp member
    rcases below with below | ⟨nulled, _⟩
    · exact (by decide : ¬([ResponsePathSegment.field "user"]).IsPrefix
        [.field "b"]) below
    · change false = true at nulled
      cases nulled

private def failed : ReferenceWorkQueue.GraphEvent := .taskFailure sharedTask 1

private def succeeded : ReferenceWorkQueue.GraphEvent :=
  .taskSuccess parentTask
    {
      value := { path := [], data := parentData, deliveryGroups := [parent] },
      work := ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty) [1, 0, 0]
    }

/-- The executable reference implementation does report the broader H failure.
Witness: exact replay promotes H after P closes, then emits H's retained error count.
This supplies the broader report required by the revised terminal contract.
-/
theorem reference_reports_broad_failure
    : ReferenceWorkQueue.inputsStarted work [[failed], [succeeded]] = true
      ∧ ((ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
          [[failed], [succeeded]]).2
        = [
          [.groupFailure deep 1],
          [
            values,
            .groupSuccess parent [hidden] [],
            .groupFailure hidden 1,
            .workQueueTermination
          ]
        ] := by
  cbv

end GraphQL.IncrementalDelivery.Tests.FailureScopes
