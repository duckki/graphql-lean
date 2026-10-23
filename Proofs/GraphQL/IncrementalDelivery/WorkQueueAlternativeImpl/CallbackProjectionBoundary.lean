import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackProjectionSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConstructorInitialization
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Sound host batch boundaries and the unchanged semantic source membership checks. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

/-- At a real batch boundary an unfinished queue has a root or a pending notice.
A raw nonterminal state with neither can emit termination on an empty batch.
-/
def Boundary (queue : ReferenceWorkQueue.State) : Prop :=
  queue.terminated = true
  ∨ (queue.rootGroups.isEmpty
      && queue.rootStreams.isEmpty
      && queue.groupFailureEvents.isEmpty)
    = false

theorem Boundary.after_batch (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    : Boundary (queue.handleGraphEvents batch).1 := by
  unfold ReferenceWorkQueue.State.handleGraphEvents
  by_cases ended : queue.terminated = true
  · simp only [ended, ↓reduceIte]
    exact Or.inl ended
  · simp only [ended, Bool.false_eq_true, ↓reduceIte]
    split
    · exact Or.inl rfl
    · exact Or.inr (Bool.eq_false_iff.mpr (by assumption))

/-- The membership/termination half of source admission, starting at an arbitrary queue. -/
def startedFrom (queue : ReferenceWorkQueue.State) : List (List GraphEvent) → Bool
  | [] => true
  | batch :: rest =>
      !queue.terminated
      && !batch.isEmpty
      && queue.acceptsBatch batch
      && startedFrom (queue.handleGraphEvents batch).1 rest

/-- The unchanged public fold is this same sequential source check. -/
theorem inputsStarted_eq (work : Work) (batches : List (List GraphEvent))
    : ReferenceWorkQueue.inputsStarted work batches
      = startedFrom
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches := by
  have fold (queue : ReferenceWorkQueue.State) (valid : Bool)
      : (batches.foldl
          (fun (state, valid) batch =>
            ((state.handleGraphEvents batch).1,
              valid && !state.terminated && !batch.isEmpty && state.acceptsBatch batch))
          (queue, valid)).2
        = (valid && startedFrom queue batches) := by
    induction batches generalizing queue valid with
    | nil => simp [startedFrom]
    | cons batch rest ih =>
        rw [List.foldl_cons, ih]
        simp only [startedFrom, Bool.and_assoc]
  exact (fold _ true).trans (Bool.true_and _)

/-- Nonempty executed work supplies the boundary condition; callers need not assume
that initial roots exist independently of execution and constructor correctness.
-/
theorem initialized_boundary {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    : Boundary
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)) := by
  let queue := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  refine Or.inr (Bool.eq_false_iff.mpr ?_)
  intro empty
  obtain ⟨rootsEmpty, _⟩ := Bool.and_eq_true_iff.mp empty
  obtain ⟨groupsEmpty, streamsEmpty⟩ := Bool.and_eq_true_iff.mp rootsEmpty
  have groups : queue.rootGroups = [] := List.isEmpty_iff.mp groupsEmpty
  have streams : queue.rootStreams = [] := List.isEmpty_iff.mp streamsEmpty
  have notices := generated.initialNotices_nonempty nonempty
  have absentGroups : queue.initialGroups = [] := by
    rw [ReferenceWorkQueue.createWorkQueue_rootGroups] at groups
    exact List.map_eq_nil_iff.mp groups
  have absentStreams : queue.initialStreams = [] := by
    cases entries : queue.initialStreams with
    | nil => rfl
    | cons stream rest =>
        have member : stream ∈ queue.initialStreams := by
          simp only [entries, List.mem_cons, true_or]
        have active := ReferenceWorkQueue.createWorkQueue_initialStreams_active
          (ReferenceWorkQueue.Work.fromExecution work) (List.mem_map_of_mem member)
        change stream.ref ∈ queue.rootStreams at active
        rw [streams] at active
        cases active
  exact notices (by rw [absentGroups, absentStreams]; rfl)

private theorem startedFrom_append_left (queue : ReferenceWorkQueue.State)
    (before after : List (List GraphEvent))
    (valid : startedFrom queue (before ++ after) = true)
    : startedFrom queue before = true := by
  induction before generalizing queue with
  | nil => rfl
  | cons batch rest ih =>
      simp only [List.cons_append, startedFrom] at valid ⊢
      obtain ⟨current, later⟩ := Bool.and_eq_true_iff.mp valid
      exact Bool.and_eq_true_iff.mpr ⟨current, ih _ later⟩

/-- A full finite semantic history supplies every prefix of its existing ofList source.
This connects the projection to the actual unchanged ValidFor contract, not a weaker
replacement source predicate. No wire/output property is included in the premise.
-/
theorem source_valid_of_laws {work : Work} (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : (EventSource.ofList inputs).ValidFor work := by
  apply EventSource.ValidFor.of_asynchronous
  refine ⟨rfl, List.nil_prefix, ?_, ?_⟩
  · intro before after earlier admitted
    exact earlier.trans admitted
  · intro before admitted
    obtain ⟨after, rfl⟩ := admitted
    refine ⟨valid.prefix ⟨after.flatten, ?_⟩, ?_⟩
    · rw [List.flatten_append]
    · rw [inputsStarted_eq] at started ⊢
      exact startedFrom_append_left _ before after started

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
