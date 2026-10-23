import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.HistoryExtension

/-! Internally accounted and failure-reported work can finish its notifications.
These are constructed continuation witnesses, not assumptions on source admission.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Closing one open node
-----------------------------------------------------------------------------------------

/-- Each failed open notification has a positive settled contributor available for
its eventual completion. This is construction evidence, not an admission assumption.
-/
def OpenFailureCauses (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts)
    : Prop :=
  ∀ ref,
    Open initial events ref
    → NodeFailed work matching events failures ref
    → ∃ errors, NodeFailureCause work (failedBefore failures events.length) ref errors

/-- An open node whose tasks are accounted for has a permitted completion. Witness:
success when healthy, or a supported positive task cause when failed; neither adds notices.
-/
theorem completion_exists
    {work initial matching events failed node kind dependencies birth}
    (known : NodeAt work node kind dependencies birth)
    (opened : Open initial events node.ref)
    (accounted : NodeAccounted work matching events failed node.ref)
    (cause
      : NodeFailed work matching events failed node.ref
        → ∃ errors,
            NodeFailureCause work (failedBefore failed events.length) node.ref errors)
    : ∃ event,
        EventAllowed work initial matching events failed event
        ∧ eventPending event = []
        ∧ eventCompleted event = [node.ref]
        ∧ ¬IsValue event := by
  classical
  by_cases failure : NodeFailed work matching events failed node.ref
  · obtain ⟨errors, counted⟩ := cause failure
    cases kind with
    | group =>
        refine ⟨.groupFailure node errors, ?_, rfl, rfl, id⟩
        simpa only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
          failedBefore_filter _ (Nat.le_refl _)]
          using And.intro ⟨dependencies, birth, known⟩ ⟨opened, failure, counted.toCauses⟩
    | stream =>
        refine ⟨.streamFailure node errors, ?_, rfl, rfl, id⟩
        simpa only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
          failedBefore_filter _ (Nat.le_refl _)]
          using And.intro ⟨dependencies, birth, known⟩ ⟨opened, failure, counted⟩
  · cases kind with
    | group =>
        refine ⟨.groupSuccess node [] [], ?_, rfl, rfl, id⟩
        simp only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
          nodeAccounted_filter (Nat.le_refl _)]
        exact ⟨
          ⟨dependencies, birth, known⟩,
          opened,
          failure,
          accounted,
          by simp [Announcements]
        ⟩
    | stream =>
        refine ⟨.streamSuccess node, ?_, rfl, rfl, id⟩
        simp only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
          nodeAccounted_filter (Nat.le_refl _)]
        exact ⟨⟨dependencies, birth, known⟩, opened, failure, accounted⟩

/-- A notice-free completion removes exactly its ref from the open frontier. Witness:
append equations for announcement and completion projections.
-/
theorem open_append_completion {initial events event closed ref}
    (pending : eventPending event = []) (completed : eventCompleted event = [closed])
    : Open initial (events ++ [event]) ref ↔ Open initial events ref ∧ ref ≠ closed := by
  simp only [Open, announcedRefs, pendingRefs, completedRefs, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, pending, completed, List.append_nil,
    List.mem_append, List.mem_singleton, not_or]
  exact and_assoc.symm

/-- A notice-free closure preserves the causes of all remaining open failures.
All recorded cuts are already in the original prefix, so appended outputs create no
new causal failure; each original selected cause remains available at the new boundary.
-/
theorem OpenFailureCauses.append_completion
    {work initial matching events failures event ref}
    (supported : OpenFailureCauses work initial matching events failures)
    (witness : FailureWitness work initial matching events failures)
    (pending : eventPending event = []) (completed : eventCompleted event = [ref])
    : OpenFailureCauses work initial matching (events ++ [event]) failures := by
  intro other opened failed
  obtain ⟨cut, recorded, _, snapshot⟩ := failed
  obtain ⟨entry, member, same⟩ := List.mem_map.mp recorded
  have bounded : cut ≤ events.length := same ▸ witness.cut_le member
  have prior : NodeFailed work matching events failures other :=
    ⟨
      cut,
      recorded,
      bounded,
      by simpa only [List.take_append_of_le_length bounded] using snapshot
    ⟩
  obtain ⟨errors, cause⟩ := supported other
    ((open_append_completion pending completed).mp opened).1 prior
  refine ⟨errors, ?_⟩
  rw [witness.failedBefore_eq (Nat.le_refl _)] at cause
  rwa [witness.failedBefore_eq (by simp)]

/-- An open ref outside a suffix's selected closure refs remains open. Witness:
announcements persist, and any new completion would contradict the selected-ref bound.
-/
theorem Open.append_unselected {initial events tail refs ref}
    (opened : Open initial events ref) (selected : (completedRefs tail).Subset refs)
    (outside : ref ∉ refs)
    : Open initial (events ++ tail) ref := by
  refine ⟨?_, ?_⟩
  · simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.append_assoc]
      using List.mem_append_left (pendingRefs tail) opened.1
  · intro closed
    rw [completedRefs, List.flatMap_append] at closed
    rcases List.mem_append.mp closed with old | new
    · exact opened.2 old
    · exact outside (selected new)

-----------------------------------------------------------------------------------------
-- Closing a finite frontier
-----------------------------------------------------------------------------------------

/-- Selected announced refs can close once their own contributing tasks are accounted
for; unrelated tasks may remain unfinished. Witness: close each still-open selected ref
once, emitting no notices or publications. The suffix closes no unselected ref, so a
future notice carrier can deliberately be left open by this existential construction.
-/
theorem Explains.close_accounted_refs {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (supported
      : OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (refs : NodeRefs)
    (announced
      : ∀ ref ∈ refs,
          ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    (accounted : ∀ ref ∈ refs, NodeAccounted work matching events failures ref)
    : ∃ tail,
        tail.length ≤ refs.length
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ Explains work groups streams (events ++ tail) matching failures
        ∧ (∀ ref ∈ refs, ref ∈ completedRefs (events ++ tail))
        ∧ (completedRefs tail).Subset refs := by
  classical
  induction refs generalizing events with
  | nil =>
      exact ⟨
        [],
        by simp,
        by simp,
        by simpa using explained,
        by simp,
        by intro other member; cases member
      ⟩
  | cons ref rest ih =>
      by_cases closed : ref ∈ completedRefs events
      · obtain ⟨tail, bounded, controls, finished, completes, selected⟩ := ih explained supported
          (fun other member => announced other (by simp [member]))
          (fun other member => accounted other (by simp [member]))
        refine ⟨tail, by simp only [List.length_cons]; omega, controls, finished, ?_, ?_⟩
        · intro other member
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [completedRefs, List.flatMap_append]
              using List.mem_append_left (completedRefs tail) closed
          · exact completes other member
        · intro other member
          exact List.mem_cons_of_mem _ (selected member)
      · have opened : Open ((groups ++ streams).map DeliveryNode.ref) events ref :=
          ⟨announced ref (by simp), closed⟩
        obtain ⟨node, kind, dependencies, birth, known, same⟩ :=
          explained.noticeFacts.supported ref opened.1
        obtain ⟨event, allowed, pending, completed, control⟩ := completion_exists known
          (same ▸ opened) (same ▸ accounted ref (by simp)) (supported node.ref (same ▸ opened))
        have extended := explained.append_event
          allowed
        obtain ⟨tail, bounded, controls, finished, completes, selected⟩ :=
          ih extended (supported.append_completion explained.2.1 pending completed)
          (fun other member => by
            simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
              List.flatMap_nil, pending, List.append_nil]
              using announced other (List.mem_cons_of_mem ref member))
          (fun other member =>
            (accounted other (List.mem_cons_of_mem ref member)).append [event])
        refine ⟨event :: tail, by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_⟩
        · intro output member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨pending, control⟩
          · exact controls output member
        · simpa only [List.append_assoc, List.singleton_append] using finished
        · intro other member
          rcases List.mem_cons.mp member with rfl | member
          · simp [completedRefs, completed, same]
          · simpa only [List.append_assoc, List.singleton_append] using completes other member
        · intro other member
          simp only [completedRefs, List.flatMap_cons, completed, same,
            List.singleton_append, List.mem_cons] at member
          exact List.mem_cons.mpr (member.imp_right (fun inTail => selected inTail))

/-- A finite list covering the open refs can be closed without new publications or
notices, once all tasks are accounted for. Witness: close each still-open ref once,
using its supported descriptor and preserving the original failure cuts and matching.
-/
theorem Explains.close_open_refs {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (supported
      : OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (remaining : NodeRefs)
    (covers
      : ∀ ref,
          Open ((groups ++ streams).map DeliveryNode.ref) events ref → ref ∈ remaining)
    : ∃ tail,
        tail.length ≤ remaining.length
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ Explains work groups streams (events ++ tail) matching failures
        ∧ ∀ ref ∈
            announcedRefs ((groups ++ streams).map DeliveryNode.ref) (events ++ tail),
            ref ∈ completedRefs (events ++ tail) := by
  classical
  induction remaining generalizing events with
  | nil =>
      refine ⟨[], by simp, by simp, by simpa using explained, ?_⟩
      intro ref announced
      by_cases closed : ref ∈ completedRefs (events ++ [])
      · exact closed
      · have opened : Open ((groups ++ streams).map DeliveryNode.ref) events ref := by
          simpa only [Open, List.append_nil] using And.intro announced closed
        exact False.elim (List.not_mem_nil (covers ref opened))
  | cons ref rest ih =>
      by_cases opened : Open ((groups ++ streams).map DeliveryNode.ref) events ref
      · obtain ⟨node, kind, dependencies, birth, known, same⟩ :=
          explained.noticeFacts.supported ref opened.1
        have nodeAccounted : NodeAccounted work matching events failures
            node.ref := by
          rintro occurrence owners ⟨producer, payload, task⟩ _
          exact accounted occurrence owners producer payload task
        obtain ⟨event, allowed, pending, completed, control⟩ :=
          completion_exists known (same ▸ opened) nodeAccounted (supported node.ref (same ▸ opened))
        have extended :=
          explained.append_event
            allowed
        have stillAccounted : ∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload →
            TaskAccounted work matching (events ++ [event]) failures occurrence :=
          fun occurrence owners producer payload task =>
            (accounted occurrence owners producer payload task).append [event]
        have nextCover : ∀ other,
            Open ((groups ++ streams).map DeliveryNode.ref) (events ++ [event]) other →
            other ∈ rest := by
          intro other active
          have facts := (open_append_completion pending completed).mp active
          rcases List.mem_cons.mp (covers other facts.1) with equal | member
          · exact False.elim (facts.2 (equal.trans same.symm))
          · exact member
        obtain ⟨tail, bounded, controls, finished, closed⟩ :=
          ih extended (supported.append_completion explained.2.1 pending completed)
            stillAccounted nextCover
        refine ⟨event :: tail, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
        · intro next member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨pending, control⟩
          · exact controls next member
        · simpa only [List.append_assoc, List.singleton_append] using finished
        · simpa only [List.append_assoc, List.singleton_append] using closed
      · obtain ⟨tail, bounded, controls, finished, closed⟩ :=
          ih explained supported accounted (by
            intro other active
            rcases List.mem_cons.mp (covers other active) with equal | member
            · exact False.elim (opened (equal ▸ active))
            · exact member)
        exact ⟨tail, Nat.le_trans bounded (by simp), controls, finished, closed⟩

/-- Once tasks are internally accounted and unpublished attachments are reported,
a terminal raw history exists. Witness:
at most one notice-free completion per currently announced ref, with unchanged failures
and publication matching. No new payload or cancellation is invented.
-/
theorem Explains.finish_accounted {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (supported
      : OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (reported
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → ¬Published matching events occurrence
          → FailureReportedFor events payload.path)
    : ∃ tail,
        tail.length
          ≤ (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events).length
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ Explains work groups streams (events ++ tail) matching failures
        ∧ Terminal work ((groups ++ streams).map DeliveryNode.ref) matching
            (events ++ tail) failures := by
  obtain ⟨tail, bounded, controls, finished, closed⟩ :=
    explained.close_open_refs supported accounted
      (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
      (fun _ opened => opened.1)
  refine ⟨tail, bounded, controls, finished, ?_⟩
  rw [Terminal]
  refine ⟨?_, ?_⟩
  · intro occurrence owners producer payload known
    by_cases published : Published matching events occurrence
    · exact Or.inr (published.append tail)
    · exact Or.inl ⟨((accounted _ _ _ _ known).resolve_right published).append tail,
        (reported _ _ _ _ known published).append tail⟩
  intro node kind dependencies birth _ announced
  exact closed node.ref announced

/-- An internally accounted, reported prefix extends to a complete run, preserving its
initialization and every existing work batch. Witness: append closures and a separate
termination batch, without changing previous value grouping or failure evidence.
-/
theorem WorkBatching.finish_accounted
    {work groups streams events matching failures batches}
    (batched : WorkBatching events batches)
    (explained : Explains work groups streams events matching failures)
    (supported
      : OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (reported
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → ¬Published matching events occurrence
          → FailureReportedFor events payload.path)
    : ∃ tail : List WorkQueueEvent,
        AdmissibleRun work
          ⟨
            groups,
            streams,
            batches ++ tail.map (fun event => [event]) ++ [[.workQueueTermination]]
          ⟩
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ tail.length
          ≤ (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events).length := by
  obtain ⟨tail, bounded, controls, finished, terminal⟩ :=
    explained.finish_accounted supported accounted reported
  refine ⟨tail, ⟨events ++ tail, matching, failures, finished, terminal, ?_⟩,
    controls, bounded⟩
  exact (batched.append (WorkBatching.singletons tail)).append
    (WorkBatching.singletons [.workQueueTermination])

/-- Terminal-run existence is exactly reachability of a history accounting for all
tasks and reporting cancelled attachments. Witness: extract terminal accounting, or
construct every remaining completion and append termination. The right side assumes
neither closed IDs nor a complete run.
-/
theorem admissibleRun_exists_iff_reported_history (work : Work)
    : (∃ history, AdmissibleRun work history)
      ↔ ∃ groups streams events matching failures,
          Explains work groups streams events matching failures
          ∧ OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref) matching
              events failures
          ∧ ∀ occurrence owners producer payload,
              TaskAt work occurrence owners producer payload
              → (TaskCancelled work matching events failures occurrence
                  ∧ FailureReportedFor events payload.path)
                ∨ Published matching events occurrence := by
  constructor
  · rintro ⟨history, events, matching, failures, explained, terminal, _⟩
    refine ⟨history.initialGroups, history.initialStreams, events, matching, failures,
      explained, ?_, terminal.1⟩
    intro ref opened _
    obtain ⟨node, kind, dependencies, birth, known, same⟩ :=
      explained.noticeFacts.supported ref opened.1
    exact (opened.2 (same ▸ terminal.2 node kind dependencies birth known
      (same ▸ opened.1))).elim
  · rintro ⟨groups, streams, events, matching, failures, explained, supported, reported⟩
    obtain ⟨tail, run, _, _⟩ := (WorkBatching.singletons events).finish_accounted
      explained supported
      (fun _ _ _ _ known => (reported _ _ _ _ known).elim
        (fun cancelled => Or.inl cancelled.1) Or.inr)
      (fun _ _ _ _ known unpublished =>
        ((reported _ _ _ _ known).resolve_right unpublished).2)
    exact ⟨_, run⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
