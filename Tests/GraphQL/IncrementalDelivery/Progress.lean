import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.LeastRefProgress
import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureReportOrigins
import Tests.GraphQL.IncrementalDelivery.WorkQueueSemantics
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling

/-! Constructed continuations: publication, failure, shared closure, and termination. -/

namespace GraphQL.IncrementalDelivery.Tests.Progress
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Correctness

/-- A singleton deferred task starts with an explained empty prefix for any outcome.
Witness: valid notices and empty failure/event evidence, not a supplied complete run.
-/
theorem single_initial (result : Result (List (Name × ResponseValue)))
    (matching : PublicationMatching)
    : Explains (WorkQueueSemantics.single result) [WorkQueueSemantics.node] [] [] matching
        [] := by
  exact ⟨WorkQueueSemantics.initialized result, by simp [FailureWitness], by simp⟩

/-- A singleton deferred outcome with positive failures has a constructed complete run.
Witness: a counted failure completion or a fresh publication, then generic finalization.
Raw zero-count failures are excluded, and no terminal-history premise is supplied.
-/
theorem single_run_exists (result : Result (List (Name × ResponseValue)))
    (positive : GraphQL.IncrementalDelivery.Semantics.BasicErrors.PositiveFailure result)
    : ∃ history, AdmissibleRun (WorkQueueSemantics.single result) history := by
  apply (admissibleRun_exists_iff_reported_history _).mpr
  have initial := single_initial result WorkQueueSemantics.matching
  have task : TaskAt (WorkQueueSemantics.single result) (.executionGroup []) [0] none
      (.object [] result) := .executionGroup .root
  have openRef : Open [0] [] 0 := by
    simp [Open, announcedRefs, pendingRefs, completedRefs]
  cases result with
  | error errors =>
      have nonzero := positive errors rfl
      obtain ⟨reportedNode, count, event, _, control, countBound, reported⟩ :=
        initial.failure_step task rfl (.root ⟨_, _, task⟩)
          (by exact ⟨0, by simp, openRef⟩) (WorkQueueSemantics.noCancellation _ _)
      have scope : FailureReportedFor [event] [] := by
        have countBound : errors ≤ count := countBound
        rcases control with rfl | rfl
        · have allowed := reported.2.2 0 (.groupFailure reportedNode count) rfl
          obtain ⟨dependencies, producer, descriptor⟩ := allowed.1
          obtain ⟨rfl, _, _, _⟩ := WorkQueueSemantics.node_single descriptor
          exact ⟨WorkQueueSemantics.node, count, by omega, ⟨[], rfl⟩, Or.inl (by simp)⟩
        · have allowed := reported.2.2 0 (.streamFailure reportedNode count) rfl
          obtain ⟨dependencies, producer, descriptor⟩ := allowed.1
          have impossible := (WorkQueueSemantics.node_single descriptor).2.1
          cases impossible
      refine ⟨[WorkQueueSemantics.node], [], [event], WorkQueueSemantics.matching,
        [(0, .executionGroup [])], reported, ?_⟩
      intro occurrence owners producer payload known
      obtain ⟨rfl, rfl, _, rfl⟩ := WorkQueueSemantics.task_single known
      refine Or.inl ⟨?_, scope⟩
      exact .of_recorded known
        (by simp)
        (by
          rintro ⟨index, observed, selected, value, _⟩
          have member := List.mem_of_getElem? selected
          simp only [List.mem_singleton] at member
          subst observed
          rcases control with rfl | rfl <;> exact value)
        (by simp [failedBefore])
  | ok value =>
      obtain ⟨data, errors⟩ := value
      have ready : CanPublish (WorkQueueSemantics.single (.ok (data, errors)))
          WorkQueueSemantics.matching [] [] (.executionGroup []) none :=
        ⟨by simp [Published], WorkQueueSemantics.noCancellation _ _, by simp, trivial⟩
      have owner : PublicationOwner (WorkQueueSemantics.single (.ok (data, errors))) [0]
          WorkQueueSemantics.matching [] [] [0]
          WorkQueueSemantics.node := by
        have opened : OpenOwner (WorkQueueSemantics.single (.ok (data, errors))) [0] [] [0]
            WorkQueueSemantics.node :=
          ⟨⟨.group, [], none, .group (group := { node := WorkQueueSemantics.node })
            .root (by simp)⟩, by simp [WorkQueueSemantics.node], openRef⟩
        refine ⟨opened, ⟨WorkQueueSemantics.node, opened, WorkQueueSemantics.noFailure _ _⟩, ?_⟩
        intro other available
        obtain ⟨kind, parents, birth, known⟩ := available.1
        simp only [(WorkQueueSemantics.node_single known).1, Nat.le_refl]
      have published := initial.publish_object task ready owner
      refine ⟨[WorkQueueSemantics.node], [], _, _, [], published, ?_⟩
      intro occurrence owners producer payload known
      obtain ⟨rfl, _, _, _⟩ := WorkQueueSemantics.task_single known
      exact Or.inr ⟨0, _, rfl, trivial, by simp [matchNext]⟩

/-- The constructed singleton runs are observations of actual conforming factories.
Witness: complete-run realization, covering both successful and failing outcomes.
-/
example (response : Response) (result : Result (List (Name × ResponseValue)))
    (positive : GraphQL.IncrementalDelivery.Semantics.BasicErrors.PositiveFailure result)
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((WorkQueueSemantics.single result).size ≠ 0
          → (scheduler (WorkQueueSemantics.single result)).Conforms
              (WorkQueueSemantics.single result))
        ∧ (executionFromWork scheduler response
            (WorkQueueSemantics.single result)).Observes
            observed true :=
  (completeObservation_exists_iff response (WorkQueueSemantics.single result)).mpr
    (Or.inr (single_run_exists result positive))

/-- One shared publication can finish both owners in at most two additional events,
preserving the already observed batch. Witness: finite-frontier completion, not an
explicitly supplied pair of success events or a selected owner-closure ordering.
-/
example
    : ∃ tail : List WorkQueueEvent,
        AdmissibleRun HistoryScheduling.shared
          ⟨
            [HistoryScheduling.left, HistoryScheduling.right],
            [],
            [[HistoryScheduling.value HistoryScheduling.left]]
            ++ tail.map (fun event => [event])
            ++ [[.workQueueTermination]]
          ⟩
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ tail.length ≤ 2 := by
  have initial : Explains HistoryScheduling.shared
      [HistoryScheduling.left, HistoryScheduling.right] [] [] HistoryScheduling.matching [] :=
    ⟨HistoryScheduling.initialized, by simp [FailureWitness], by simp⟩
  have published :=
    initial.append_event
      (by
        simpa [failedBefore, HistoryScheduling.left, HistoryScheduling.right]
          using HistoryScheduling.publishes HistoryScheduling.left (by simp))
  have accounted : ∀ occurrence owners producer payload,
      TaskAt HistoryScheduling.shared occurrence owners producer payload →
      TaskAccounted HistoryScheduling.shared HistoryScheduling.matching
        [HistoryScheduling.value HistoryScheduling.left] [] occurrence := by
    intro occurrence owners producer payload known
    have same := HistoryScheduling.task_shared known
    subst occurrence
    exact Or.inr ⟨0, _, rfl, trivial, rfl⟩
  have completed := (WorkBatching.singletons
    [HistoryScheduling.value HistoryScheduling.left]).finish_accounted published
      (by simpa [failedBefore] using accounted)
      (by
        intro occurrence owners producer payload known unpublished
        have cancelled := (accounted _ _ _ _ known).resolve_right unpublished
        exact False.elim (cancelled.nonempty rfl))
  simpa [announcedRefs, pendingRefs, eventPending, HistoryScheduling.value]
    using completed

/-- Selected closure can reserve the other shared owner for a later notice carrier.
Witness: close ref zero despite its repeated selection, while ref one remains open.
-/
example
    : ∃ tail : List WorkQueueEvent,
        Explains HistoryScheduling.shared
          [HistoryScheduling.left, HistoryScheduling.right] []
          ([HistoryScheduling.value HistoryScheduling.left] ++ tail)
          HistoryScheduling.matching []
        ∧ 0 ∈ completedRefs ([HistoryScheduling.value HistoryScheduling.left] ++ tail)
        ∧ Open [0, 1] ([HistoryScheduling.value HistoryScheduling.left] ++ tail) 1
        ∧ tail.length ≤ 2 := by
  have initial : Explains HistoryScheduling.shared
      [HistoryScheduling.left, HistoryScheduling.right] [] [] HistoryScheduling.matching [] :=
    ⟨HistoryScheduling.initialized, by simp [FailureWitness], by simp⟩
  have published :=
    initial.append_event
      (by
        simpa [failedBefore, HistoryScheduling.left, HistoryScheduling.right]
          using HistoryScheduling.publishes HistoryScheduling.left (by simp))
  obtain ⟨tail, bounded, _, finished, closes, selected⟩ :=
    published.close_accounted_refs [0, 0]
      (by simp [announcedRefs, pendingRefs, HistoryScheduling.left, HistoryScheduling.right,
        eventPending, HistoryScheduling.value])
      (by
        intro ref member occurrence owners projected _
        obtain ⟨producer, payload, known⟩ := projected
        have same := HistoryScheduling.task_shared known
        subst occurrence
        exact Or.inr ⟨0, _, rfl, trivial, rfl⟩)
  have opened : Open [0, 1] [HistoryScheduling.value HistoryScheduling.left] 1 := by
    simp [Open, announcedRefs, pendingRefs, completedRefs, eventPending, eventCompleted,
      HistoryScheduling.value]
  exact ⟨
    tail,
    finished,
    closes 0 (by simp),
    opened.append_unselected selected (by simp),
    bounded
  ⟩

/-- Updating the next publication index leaves all prior task identities unchanged.
Witness: strict-index prefix agreement, even when payload values are equal.
-/
example (matching : PublicationMatching) (occurrence : Occurrence) (index before : Nat)
    (earlier : before < index)
    : matchNext matching index occurrence before = matching before :=
  (matchNext_before matching occurrence earlier).symm

/-- A justified failure makes an observable step reporting at least its actual count.
Witness: the generic failure-step constructor from an initialized, nonterminal prefix.
-/
example
    : ∃ node errors event,
        node.ref ∈ [0]
        ∧ (event = .groupFailure node errors ∨ event = .streamFailure node errors)
        ∧ 2 ≤ errors
        ∧ Explains WorkQueueSemantics.failingWork [WorkQueueSemantics.node] [] [event]
            WorkQueueSemantics.matching [(0, .executionGroup [])] := by
  have initial := single_initial (.error 2) WorkQueueSemantics.matching
  have task : TaskAt WorkQueueSemantics.failingWork (.executionGroup []) [0] none
      (.object [] (.error 2)) := .executionGroup .root
  exact initial.failure_step task rfl (.root ⟨_, _, task⟩)
    ⟨
      0,
      by simp,
      by simp [Open, announcedRefs, pendingRefs, completedRefs,
        WorkQueueSemantics.node]
    ⟩ (WorkQueueSemantics.noCancellation _ _)

/-- A failure recorded after two outputs cannot retroactively affect the first output.
Witness: direct boundary evaluation; equal-boundary cuts are visible only at that cut.
-/
example
    : failedBefore [(0, .executionGroup [0]), (2, .executionGroup [1])] 1
      = [.executionGroup [0]] :=
  rfl

/-- The same cut is visible at the boundary where a subsequent failure notice uses it. -/
example
    : failedBefore [(0, .executionGroup [0]), (2, .executionGroup [1])] 2
      = [.executionGroup [0], .executionGroup [1]] :=
  rfl

/-- An already-closed raw history needs no additional completion events. Witness: the empty
open frontier, while all previous publications and failures remain unchanged.
-/
example
    : ∃ tail,
        tail.length ≤ 0
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ Explains WorkQueueSemantics.work [WorkQueueSemantics.node] []
            (WorkQueueSemantics.events ++ tail) WorkQueueSemantics.matching []
        ∧ ∀ ref ∈ announcedRefs [0] (WorkQueueSemantics.events ++ tail),
            ref ∈ completedRefs (WorkQueueSemantics.events ++ tail) := by
  apply WorkQueueSemantics.explained.close_open_refs
    (by
      intro occurrence owners producer payload known
      exact (WorkQueueSemantics.terminal.1 _ _ _ _ known).imp_left And.left) []
  intro ref opened
  exact False.elim
    (opened.2
      (WorkQueueSemantics.explained.allCompleted
        (by
          simpa [WorkQueueSemantics.node, failedBefore] using WorkQueueSemantics.terminal)
        ref opened.1))

/-- Equal-valued stream items have separate publication tokens, but share one closure.
Witness: the structural item ordinals, independent of payload equality.
-/
example
    : observationTokens []
        (.stream WorkQueueSemantics.node
          [(.ok (.null, 0), .empty), (.ok (.null, 0), .empty)])
      = [.inr 0, .inl (.item [] 0), .inl (.item [] 1)] := by
  simp [observationTokens, List.finRange_succ, WorkQueueSemantics.node]

/-- Shared owners consume one publication token and two independent completion tokens.
Witness: the raw structural inventory, before any owner or schedule is selected.
-/
example : (observationTokens [] HistoryScheduling.shared).length = 3 := by
  simp [observationTokens, HistoryScheduling.shared]

/-- Every history of a singleton deferred task has at most two nonterminal atoms,
whether the fixed outcome succeeds or fails. Witness: the uniform inventory bound.
-/
example (result : Result (List (Name × ResponseValue)))
    {groups streams events matching cuts}
    (explained
      : Explains (WorkQueueSemantics.single result) groups streams events matching cuts)
    : events.length ≤ 2 := by
  simpa [WorkQueueSemantics.single, observationTokens]
    using explained.length_le_observationTokens

/-- Batching cannot exceed the three possible shared-work actions plus termination.
Witness: the complete-run bound, independent of value grouping and batching choices.
-/
example {history} (admitted : AdmissibleRun HistoryScheduling.shared history)
    : history.batches.length ≤ 4 := by
  simpa [HistoryScheduling.shared, observationTokens]
    using admitted.length_le_observationTokens

/-- Even a failed singleton initialization admits a maximal finite continuation.
Witness: bounded existential extension, not a deterministic future trace.
-/
example
    : ∃ events matching cuts,
        Explains WorkQueueSemantics.failingWork [WorkQueueSemantics.node] [] events
          matching cuts
        ∧ ∀ suffix next nextCuts,
            Explains WorkQueueSemantics.failingWork [WorkQueueSemantics.node] []
              (events ++ suffix) next nextCuts
            → suffix = [] := by
  simpa only [WorkQueueSemantics.failingWork, List.nil_append]
    using (single_initial (.error 2) WorkQueueSemantics.matching).maximal_extension

/-- A high-ordinal item still precedes a task inside its child subtree. Witness: edge
weight includes the parent item index; plain address length would not order all items.
-/
example
    : (Occurrence.item [3, 0] 7).dependencyRank
      < (Occurrence.executionGroup [3, 0, 7]).dependencyRank := by decide

/-- Equal-valued stream items share cancellation prerequisites but not publication IDs.
Witness: their equal owner/producer projections and the generic causal transport lemma.
-/
example (failures : FailureCuts) (matching : PublicationMatching)
    (events : List WorkQueueEvent)
    (cancelled
      : TaskCancelled HistoryScheduling.items matching events failures (.item [] 0))
    (unpublished : ¬Published matching events (.item [] 1))
    : TaskCancelled HistoryScheduling.items matching events failures (.item [] 1) :=
  cancelled.same_prerequisites (TaskAt.item .root rfl) (TaskAt.item .root rfl) unpublished

/-- Starting from an unaccounted second item finds a structurally ready task, despite
that second item itself waiting for its predecessor. Witness: dependency-rank descent.
-/
example
    : ∃ occurrence owners producer payload,
        TaskAt HistoryScheduling.items occurrence owners producer payload
        ∧ CanPublish HistoryScheduling.items HistoryScheduling.itemMatching [] []
            occurrence producer := by
  apply readyTask_exists (occurrence := .item [] 1) (TaskAt.item .root rfl)
  rintro (cancelled | published)
  · exact cancelled.nonempty rfl
  · simp [Published] at published

/-- Finite streams with positive failures admit a complete run without supplied history.
Witness: generic root accounting followed by actual failure-reporting closures.
-/
example (node : DeliveryNode) (results : List (Result ResponseValue))
    (positive
      : ∀ result ∈ results,
          GraphQL.IncrementalDelivery.Semantics.BasicErrors.PositiveFailure result)
    : ∃ history,
        AdmissibleRun (.stream node (results.map (fun result => (result, .empty))))
          history := by
  apply childFreeStream_completeRun_exists
  · intro item member
    obtain ⟨result, _, rfl⟩ := List.mem_map.mp member
    rfl
  · induction results with
    | nil => trivial
    | cons result rest ih =>
        exact ⟨
          positive result (by simp),
          trivial,
          ih (fun result member => positive result (List.mem_cons_of_mem _ member))
        ⟩

/-- Positive stream failures realize complete observations through a conforming factory.
Witness: the reporting-aware stream existence theorem and complete-run realization.
-/
example (response : Response) (node : DeliveryNode)
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((Work.stream node [(.ok (.null, 0), .empty), (.error 1, .empty)]).size ≠ 0
          → (scheduler
              (.stream node [(.ok (.null, 0), .empty), (.error 1, .empty)])).Conforms
              (.stream node [(.ok (.null, 0), .empty), (.error 1, .empty)]))
        ∧ (executionFromWork scheduler response
            (.stream node [(.ok (.null, 0), .empty), (.error 1, .empty)])).Observes
            observed true := by
  apply (completeObservation_exists_iff _ _).mpr
  apply Or.inr
  apply childFreeStream_completeRun_exists
  · simp
  · simp [ExecutionErrors.ItemsPositive, ExecutionErrors.WorkPositive,
      GraphQL.IncrementalDelivery.Semantics.BasicErrors.PositiveFailure]

/-- Empty streams still admit a complete lifecycle. Witness: closing the announced
boundary without publishing an item or recording a failure.
-/
example (node : DeliveryNode) : ∃ history, AdmissibleRun (.stream node []) history :=
  childFreeStream_completeRun_exists node [] (by simp) trivial

/-- Zero-count completion notices cannot report missing data. Witness: the observable
reporting predicate requires a strictly positive error count.
-/
example (node : DeliveryNode) (path : ResponsePath)
    : ¬FailureReportedFor [.streamFailure node 0] path := by
  rintro ⟨reported, errors, positive, _, group | stream⟩
  · simp at group
  · simp only [List.mem_singleton, WorkQueueEvent.streamFailure.injEq] at stream
    omega

/-- The failure fixture is explained independently of its terminal-reporting witness.
Witness: its actual counted completion and separately licensed settlement cut.
-/
private theorem singleton_failed_explained
    : Explains WorkQueueSemantics.failingWork [WorkQueueSemantics.node] []
        [WorkQueueSemantics.failure] WorkQueueSemantics.matching
        [(0, .executionGroup [])] := by
  refine ⟨WorkQueueSemantics.initialized _, WorkQueueSemantics.failureWitness _, ?_⟩
  intro index event selected
  cases index with
  | zero =>
      have same : event = WorkQueueSemantics.failure := by simpa using selected.symm
      subst event
      simpa [failedBefore, WorkQueueSemantics.node]
        using WorkQueueSemantics.reportsFailure
  | succ index => simp at selected

/-- A failed singleton's sole owner is open at settlement, without an openness premise.
Witness: the earlier-settlement prefix excludes prior cancellation and fixed failure
excludes publication; either kind of prior completion would contradict licensing.
-/
example : Open [0] [] 0 := by
  exact singleton_failed_explained.singleton_failure_open (cut := 0) (by simp)
    (show TaskAt WorkQueueSemantics.failingWork (.executionGroup []) [0] none
            (.object [] (.error 2)) from .executionGroup .root)

/-- Accepted settlement is impossible after every contributing owner has completed.
Witness: the licensing prefix retains a healthy unfinished owner, whether open or latent.
This permits shared settlement after one owner closes without admitting fully dead work.
-/
example
    {work groups streams events matching before cut occurrence after owners producer
      payload}
    (known : TaskAt work occurrence owners producer payload)
    (closed : ∀ ref ∈ owners, ref ∈ completedRefs (events.take cut))
    : ¬Explains work groups streams events matching
        (before ++ (cut, occurrence) :: after) := by
  intro explained
  obtain ⟨ref, member, _, unfinished⟩ := explained.failure_outstanding_owner known
  exact unfinished (closed ref member)

/-- Closing the singleton ID produces a covering report without assuming Terminal.
Witness: generated-style owner paths, the actual cut, and observable ID closure alone.
-/
example : FailureReportedFor [WorkQueueSemantics.failure] [] := by
  apply Explains.singleton_recorded_task_reported (paths := fun _ => []) (bound := 1)
    (work := WorkQueueSemantics.failingWork)
    (by
      simp [Semantics.MixedOwnerPaths.WorkAt, Semantics.OwnerPaths.MapAt,
        Semantics.OwnerPaths.Assigned, Semantics.OwnerPaths.mapNodes,
        Semantics.OwnerPaths.fragmentNodes, Semantics.Below, WorkQueueSemantics.failingWork,
        WorkQueueSemantics.single, WorkQueueSemantics.node])
    singleton_failed_explained (cut := 0) (occurrence := .executionGroup []) (ref := 0)
    (producer := none) (payload := .object [] (.error 2))
  · intro ref member
    simpa [announcedRefs, pendingRefs, completedRefs, eventCompleted, eventPending,
      WorkQueueSemantics.failure] using member
  · simp
  · exact .executionGroup .root
  · decide

#print axioms accountedHistory_exists_of_initial_owner_coverage
#print axioms childFreeStream_closed_reports
#print axioms childFreeStream_completeRun_exists
#print axioms single_run_exists
#print axioms maximal_no_eligible_accounted_and_closed
#print axioms Explains.before_settlement
#print axioms Explains.singleton_failure_open
#print axioms Explains.singleton_recorded_task_reported
#print axioms Explains.failure_outstanding_owner
#print axioms Explains.failure_latent_owner

end GraphQL.IncrementalDelivery.Tests.Progress
