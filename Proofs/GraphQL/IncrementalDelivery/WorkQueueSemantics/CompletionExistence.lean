import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.HistoryExtension

/-! Accounted work can always finish its remaining notifications and terminate.
These are constructed continuation witnesses, not assumptions on source admission.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Closing one open node
-----------------------------------------------------------------------------------------

/-- An open node whose tasks are accounted for has a permitted completion. Witness:
success when healthy, or its finite contribution sum when failed; neither adds notices.
-/
theorem completion_exists
    {work initial matching events failed node kind dependencies birth}
    (known : NodeAt work node kind dependencies birth)
    (opened : Open initial events node.ref)
    (accounted : NodeAccounted work matching events failed node.ref)
    (failuresKnown
      : ∀ occurrence ∈ failedBefore failed events.length,
          ∃ owners producer payload, TaskAt work occurrence owners producer payload)
    : ∃ event,
        EventAllowed work initial matching events failed event
        ∧ eventPending event = []
        ∧ eventCompleted event = [node.ref]
        ∧ ¬IsValue event := by
  classical
  by_cases failure : NodeFailed work matching events failed node.ref
  · obtain ⟨errors, counted⟩ := NodeErrors.exists failuresKnown node.ref
    cases kind with
    | group =>
        refine ⟨.groupFailure node errors, ?_, rfl, rfl, id⟩
        simpa only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
          failedBefore_filter _ (Nat.le_refl _)]
          using And.intro ⟨dependencies, birth, known⟩ ⟨opened, failure, counted⟩
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
      · obtain ⟨tail, bounded, controls, finished, completes, selected⟩ := ih explained
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
          (same ▸ opened) (same ▸ accounted ref (by simp)) (by simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)]
            using explained.2.1.known)
        have extended := explained.append_event
          allowed
        obtain ⟨tail, bounded, controls, finished, completes, selected⟩ := ih extended
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
          completion_exists known (same ▸ opened) nodeAccounted (by simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)]
            using explained.2.1.known)
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
          ih extended stillAccounted nextCover
        refine ⟨event :: tail, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
        · intro next member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨pending, control⟩
          · exact controls next member
        · simpa only [List.append_assoc, List.singleton_append] using finished
        · simpa only [List.append_assoc, List.singleton_append] using closed
      · obtain ⟨tail, bounded, controls, finished, closed⟩ :=
          ih explained accounted (by
            intro other active
            rcases List.mem_cons.mp (covers other active) with equal | member
            · exact False.elim (opened (equal ▸ active))
            · exact member)
        exact ⟨tail, Nat.le_trans bounded (by simp), controls, finished, closed⟩

/-- Once every task is published or cancelled, a terminal raw history exists. Witness:
at most one notice-free completion per currently announced ref, with unchanged failures
and publication matching. No new payload or cancellation is invented.
-/
theorem Explains.finish_accounted {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    : ∃ tail,
        tail.length
          ≤ (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events).length
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ Explains work groups streams (events ++ tail) matching failures
        ∧ Terminal work ((groups ++ streams).map DeliveryNode.ref) matching
            (events ++ tail) failures := by
  obtain ⟨tail, bounded, controls, finished, closed⟩ :=
    explained.close_open_refs accounted
      (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
      (fun _ opened => opened.1)
  refine ⟨tail, bounded, controls, finished, ?_⟩
  rw [Terminal]
  have finalAccounting : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload →
      TaskAccounted work matching (events ++ tail) failures occurrence :=
    fun occurrence owners producer payload task =>
      (accounted occurrence owners producer payload task).append tail
  refine ⟨finalAccounting, ?_⟩
  intro node kind dependencies birth _
  by_cases announced : node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref)
      (events ++ tail)
  · exact Or.inl (closed node.ref announced)
  · refine Or.inr ⟨announced, Or.inr ?_⟩
    rintro occurrence owners ⟨producer, payload, task⟩ _
    exact finalAccounting occurrence owners producer payload task

/-- An accounted admitted prefix extends to a complete run, preserving its initialization
and every existing work batch. Witness: append the constructed closures and a separate
termination batch, without changing previous value grouping or failure evidence.
-/
theorem WorkBatching.finish_accounted
    {work groups streams events matching failures batches}
    (batched : WorkBatching events batches)
    (explained : Explains work groups streams events matching failures)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
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
  obtain ⟨tail, bounded, controls, finished, terminal⟩ := explained.finish_accounted accounted
  refine ⟨tail, ⟨events ++ tail, matching, failures, finished, terminal, ?_⟩,
    controls, bounded⟩
  exact (batched.append (WorkBatching.singletons tail)).append
    (WorkBatching.singletons [.workQueueTermination])

/-- Terminal-run existence is exactly reachability of a history accounting for all
tasks. Witness: extract terminal accounting, or construct every remaining completion
and append termination. The right side assumes neither closed IDs nor a complete run.
-/
theorem admissibleRun_exists_iff_accounted_history (work : Work)
    : (∃ history, AdmissibleRun work history)
      ↔ ∃ groups streams events matching failures,
          Explains work groups streams events matching failures
          ∧ ∀ occurrence owners producer payload,
              TaskAt work occurrence owners producer payload
              → TaskAccounted work matching events failures occurrence := by
  constructor
  · rintro ⟨history, events, matching, failures, explained, terminal, _⟩
    exact ⟨history.initialGroups, history.initialStreams, events, matching, failures,
      explained, terminal.1⟩
  · rintro ⟨groups, streams, events, matching, failures, explained, accounted⟩
    obtain ⟨tail, run, _, _⟩ := (WorkBatching.singletons events).finish_accounted
      explained accounted
    exact ⟨_, run⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
