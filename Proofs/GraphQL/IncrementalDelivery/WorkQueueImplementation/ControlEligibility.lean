import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CacheEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingFailureFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! Fresh internal controls retain their queued-head permission until their own dispatch. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence)

/-- Appending notices cannot overtake an existing queued head. A different closure cannot
consume that head; the matching control remains eligible at its actual dispatch cut. -/
theorem State.dispatchGraphEvent_preserves_control (queue : State) (event : GraphEvent)
    (notice : GroupFailureEvent) (available : List (Occurrence × Nat))
    (accepted : queue.acceptsGraphEvent (.groupFailure notice) = true)
    (fresh : notice.group.ref ∉ event.identities.2)
    : (queue.dispatchGraphEvent event available).1.acceptsGraphEvent
        (.groupFailure notice)
      = true := by
  have head : ∃ first rest, queue.groupFailureEvents = first :: rest
      ∧ first.group.ref = notice.group.ref ∧ first.errors = notice.errors := by
    cases queued : queue.groupFailureEvents with
    | nil => simp [State.acceptsGraphEvent, queued] at accepted
    | cons first rest =>
        simp only [State.acceptsGraphEvent, queued, List.head?_cons, Option.any_some,
          Bool.and_eq_true, beq_iff_eq] at accepted
        exact ⟨first, rest, rfl, accepted⟩
  obtain ⟨first, rest, queued, sameRef, sameErrors⟩ := head
  by_cases control : ∃ supplied, event = .groupFailure supplied
  · obtain ⟨supplied, rfl⟩ := control
    have different : first.group.ref ≠ supplied.group.ref := by
      simpa only [GraphEvent.identities, List.mem_singleton, sameRef] using fresh
    have guard : (first.group.ref == supplied.group.ref && first.errors == supplied.errors)
        = false := by simp only [beq_eq_false_iff_ne.mpr different, Bool.false_and]
    simp only [State.dispatchGraphEvent, State.handleGraphEvent, State.groupFailure,
      State.cacheTaskFailures_groupFailureEvents, queued, guard, Bool.false_eq_true,
      ↓reduceIte, State.enqueueGroupFailures, List.append_nil]
    simpa only [State.acceptsGraphEvent, queued] using accepted
  · have preserved := queue.handleGraphEvent_groupFailureEvents_eq event available
      (fun other equal => control ⟨other, equal⟩)
    simp only [State.dispatchGraphEvent, State.enqueueGroupFailures, State.acceptsGraphEvent,
      preserved, queued, List.cons_append, List.head?_cons, Option.any_some,
      sameRef, sameErrors, BEq.rfl, Bool.and_self]

/-- Batch-entry permission admits ordinary callbacks. Internal controls additionally use
the source's nonrepeating closure identities to retain current-head permission. -/
theorem State.acceptsBatch_of_entry (queue : State) (events : List GraphEvent)
    (accepted : ∀ event ∈ events, queue.acceptsGraphEvent event = true)
    (unique : (events.flatMap (fun event => event.identities.2)).Nodup)
    : queue.acceptsBatch events = true := by
  have loop (remaining : List GraphEvent) (current : State) (earlier : GraphEvent → Bool)
      (available : List (Occurrence × Nat))
      (entry : ∀ event ∈ remaining, (earlier event || current.acceptsGraphEvent event) = true)
      (controls : ∀ notice, .groupFailure notice ∈ remaining
        → current.acceptsGraphEvent (.groupFailure notice) = true)
      (distinct : (remaining.flatMap (fun event => event.identities.2)).Nodup)
      : State.acceptsBatch.go earlier available current remaining = true := by
    induction remaining generalizing current earlier with
    | nil => rfl
    | cons event rest ih =>
        have permitted : (match event with
            | .groupFailure _ => current.acceptsGraphEvent event
            | _ => earlier event || current.acceptsGraphEvent event) = true := by
          cases event with
          | groupFailure notice => exact controls notice List.mem_cons_self
          | taskSuccess | taskFailure | streamItems | streamSuccess | streamFailure =>
              exact entry _ List.mem_cons_self
        have disjoint := (List.nodup_append.mp distinct).2.2
        have later (notice : GroupFailureEvent) (member : .groupFailure notice ∈ rest)
            : (current.dispatchGraphEvent event available).1.acceptsGraphEvent
                (.groupFailure notice) = true := by
          apply current.dispatchGraphEvent_preserves_control event notice available
            (controls notice (List.mem_cons_of_mem _ member))
          intro closed
          exact disjoint notice.group.ref closed notice.group.ref
            (List.mem_flatMap.mpr ⟨.groupFailure notice, member, List.mem_singleton_self _⟩) rfl
        simp only [State.acceptsBatch.go]
        apply Bool.and_eq_true_iff.mpr
        refine ⟨
          ?_,
          ih _ _ (fun next member => ?_) later (List.nodup_append.mp distinct).2.1
        ⟩
        · cases event <;> exact permitted
        · simp only [entry next (List.mem_cons_of_mem _ member), Bool.true_or]
  exact loop events queue (fun _ => false) _
    (fun event member => by simp only [Bool.false_or]; exact accepted event member)
    (fun notice member => accepted _ member) unique

/-- Earlier nonmatching callbacks cannot consume a pending control, even across a host
batch boundary. Termination bookkeeping does not alter the retained notice FIFO. -/
theorem State.handleGraphEvents_preserves_control (queue : State)
    (events : List GraphEvent) (notice : GroupFailureEvent)
    (accepted : queue.acceptsGraphEvent (.groupFailure notice) = true)
    (fresh : notice.group.ref ∉ events.flatMap (fun event => event.identities.2))
    : (queue.handleGraphEvents events).1.acceptsGraphEvent (.groupFailure notice)
      = true := by
  have loop (events : List GraphEvent) (current : State)
      (available : List (Occurrence × Nat))
      (active : current.acceptsGraphEvent (.groupFailure notice) = true)
      (unclosed : notice.group.ref ∉ events.flatMap (fun event => event.identities.2))
      : (current.replayGraphEvents events available).acceptsGraphEvent (.groupFailure notice)
        = true := by
    induction events generalizing current with
    | nil => exact active
    | cons event rest ih =>
        exact ih _ (current.dispatchGraphEvent_preserves_control event notice available active
          (fun member => unclosed (List.mem_append_left _ member)))
          (fun member => unclosed (List.mem_append_right _ member))
  cases ended : queue.terminated with
  | true => simpa only [State.handleGraphEvents, ended, ↓reduceIte] using accepted
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events ended
      rw [same]
      exact loop events queue _ accepted fresh

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
