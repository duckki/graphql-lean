import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamExistence
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

/-- A complete run is constructed for every singleton deferred outcome, including raw
zero-count failures. Witness: either one justified failure cut, or a fresh publication,
then generic finite-frontier completion. No terminal-history premise is supplied.
-/
theorem single_run_exists (result : Result (List (Name × ResponseValue)))
    : ∃ history, AdmissibleRun (WorkQueueSemantics.single result) history := by
  apply (admissibleRun_exists_iff_accounted_history _).mpr
  have initial := single_initial result WorkQueueSemantics.matching
  have task : TaskAt (WorkQueueSemantics.single result) (.executionGroup []) [0] none
      (.object [] result) := .executionGroup .root
  have openKey : Open [0] [] 0 := by
    simp [Open, announcedKeys, pendingKeys, completedKeys]
  cases result with
  | error errors =>
      have recorded := initial.record_failure task rfl (.root ⟨_, _, task⟩)
        (by exact ⟨0, by simp, openKey⟩) (WorkQueueSemantics.noCancellation _ _)
      refine ⟨[WorkQueueSemantics.node], [], [], WorkQueueSemantics.matching,
        [(0, .executionGroup [])], recorded, ?_⟩
      intro occurrence owners producer payload known
      obtain ⟨rfl, rfl, _, _⟩ := WorkQueueSemantics.task_single known
      exact Or.inl
        (.of_recorded known (by simp) (by simp [Published]) (by simp [failedBefore]))
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
            .root (by simp)⟩, by simp [WorkQueueSemantics.node], openKey⟩
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
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((WorkQueueSemantics.single result).size ≠ 0
          → (scheduler (WorkQueueSemantics.single result)).Conforms
              (WorkQueueSemantics.single result))
        ∧ (executionFromWork scheduler response
            (WorkQueueSemantics.single result)).Observes
            observed true :=
  (completeObservation_exists_iff response (WorkQueueSemantics.single result)).mpr
    (Or.inr (single_run_exists result))

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
  simpa [announcedKeys, pendingKeys, eventPending, HistoryScheduling.value]
    using completed

/-- Selected closure can reserve the other shared owner for a later notice carrier.
Witness: close key zero despite its repeated selection, while key one remains open.
-/
example
    : ∃ tail : List WorkQueueEvent,
        Explains HistoryScheduling.shared
          [HistoryScheduling.left, HistoryScheduling.right] []
          ([HistoryScheduling.value HistoryScheduling.left] ++ tail)
          HistoryScheduling.matching []
        ∧ 0 ∈ completedKeys ([HistoryScheduling.value HistoryScheduling.left] ++ tail)
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
    published.close_accounted_keys [0, 0]
      (by simp [announcedKeys, pendingKeys, HistoryScheduling.left, HistoryScheduling.right,
        eventPending, HistoryScheduling.value])
      (by
        intro key member occurrence owners projected _
        obtain ⟨producer, payload, known⟩ := projected
        have same := HistoryScheduling.task_shared known
        subst occurrence
        exact Or.inr ⟨0, _, rfl, trivial, rfl⟩)
  have opened : Open [0, 1] [HistoryScheduling.value HistoryScheduling.left] 1 := by
    simp [Open, announcedKeys, pendingKeys, completedKeys, eventPending, eventCompleted,
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
        node.key ∈ [0]
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
      by simp [Open, announcedKeys, pendingKeys, completedKeys,
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
        ∧ ∀ key ∈ announcedKeys [0] (WorkQueueSemantics.events ++ tail),
            key ∈ completedKeys (WorkQueueSemantics.events ++ tail) := by
  apply WorkQueueSemantics.explained.close_open_keys
    (by
      simpa [failedBefore, WorkQueueSemantics.node]
        using WorkQueueSemantics.terminal.1) []
  intro key opened
  exact False.elim
    (opened.2
      (WorkQueueSemantics.explained.allCompleted
        (by
          simpa [WorkQueueSemantics.node, failedBefore] using WorkQueueSemantics.terminal)
        key opened.1))

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

/-- Arbitrary finite stream outcomes, not just successful or distinct values, admit a
complete run without supplied history evidence. Witness: generic owner-coverage progress.
-/
example (node : DeliveryNode) (results : List (Result ResponseValue))
    : ∃ history,
        AdmissibleRun (.stream node (results.map (fun result => (result, .empty))))
          history := by
  apply childFreeStream_completeRun_exists
  intro item member
  obtain ⟨result, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- The stream existence theorem realizes complete wire observations through a conforming
queue constructor, including zero-count raw failures. Witness: the general complete-run bridge.
-/
example (response : Response) (node : DeliveryNode)
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((Work.stream node [(.ok (.null, 0), .empty), (.error 0, .empty)]).size ≠ 0
          → (scheduler
              (.stream node [(.ok (.null, 0), .empty), (.error 0, .empty)])).Conforms
              (.stream node [(.ok (.null, 0), .empty), (.error 0, .empty)]))
        ∧ (executionFromWork scheduler response
            (.stream node [(.ok (.null, 0), .empty), (.error 0, .empty)])).Observes
            observed true := by
  apply (completeObservation_exists_iff _ _).mpr
  apply Or.inr
  apply childFreeStream_completeRun_exists
  simp

end GraphQL.IncrementalDelivery.Tests.Progress
