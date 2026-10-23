import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkHandlers

/-! Complete parent links in actual source-event and normalized-batch replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Bundle the independent registration facts needed by the concrete handler induction
-----------------------------------------------------------------------------------------

/-- Proof-only induction package for complete links and their registration prerequisites.
`queue` is the actual executable state; `parents` is the fixed source-work assignment.
-/
private structure ParentLinkFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs)
    : Prop where
  unique : queue.GroupRefsUnique
  registration : queue.RegistrationFrame work
  closed : queue.ParentRegistryClosed parents
  complete : queue.ParentLinksComplete parents

/-- One matched source event preserves the whole concrete registration package.
Witness: independent ref/registry preservation plus complete-link handler preservation.
-/
private theorem ParentLinkFrame.handleGraphEvent {queue : State} {work parents}
    (frame : ParentLinkFrame queue work parents) (event : GraphEvent)
    (matching : event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : ParentLinkFrame (queue.handleGraphEvent event available).1 work parents := by
  exact ⟨frame.unique.handleGraphEvent event available,
    (frame.registration.handleGraphEvent event matching available).1,
    frame.closed.handleGraphEvent frame.registration.live frame.registration.tasks frame.registration event matching canonical available,
    frame.complete.handleGraphEvent frame.unique frame.registration.live frame.registration.tasks frame.registration frame.closed
      event matching canonical available⟩

/-- Enqueue effects change no group link or registration fields. -/
private theorem ParentLinkFrame.dispatchGraphEvent {queue : State} {work parents}
    (frame : ParentLinkFrame queue work parents) (event : GraphEvent)
    (matching : event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : ParentLinkFrame (queue.dispatchGraphEvent event available).1 work parents := by
  have next := frame.handleGraphEvent event matching canonical available
  exact ⟨next.unique, (frame.registration.dispatchGraphEvent event matching available).1,
    next.closed, next.complete⟩

/-- Raw event replay preserves complete links and registration prerequisites together.
Witness: induction over the actual executable state fold, not an assumed abstract run.
-/
private theorem ParentLinkFrame.replayGraphEvents {queue : State} {work parents}
    (frame : ParentLinkFrame queue work parents) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : ParentLinkFrame (queue.replayGraphEvents events available) work parents := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      exact ih (frame.dispatchGraphEvent event (matching event List.mem_cons_self)
        canonical available)
        (fun next member => matching next (List.mem_cons_of_mem _ member))

/-- Batch handling preserves the package, including skipped and terminal branches.
Witness: raw handler induction; output accumulation and the final done flag are irrelevant
to the group-node map and permanent registration fields.
-/
private theorem ParentLinkFrame.handleGraphEvents {queue : State} {work parents}
    (frame : ParentLinkFrame queue work parents) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : ParentLinkFrame (queue.handleGraphEvents events).1 work parents := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact frame
  · have replayed := frame.replayGraphEvents events matching canonical
      (GraphEvent.availableFailures events)
    dsimp only
    simp only [State.rawEventReplay_state _ _ (GraphEvent.availableFailures events)]
    split
    · exact ⟨replayed.unique, replayed.registration.withTerminated true, replayed.closed, replayed.complete⟩
    · exact replayed

-----------------------------------------------------------------------------------------
-- The generated source assignment supplies the certificate at every real replay boundary
-----------------------------------------------------------------------------------------

/-- Complete canonical parent links survive every prefix of matched raw source events.
Witness: the concrete registration frame induction, without source start or output admission.
-/
theorem State.ParentLinksComplete.replayGraphEvents {queue : State} {work parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (_live : queue.LiveGroupsRegistered) (_tasks : queue.TaskGroupsRegistered)
    (registration : queue.RegistrationFrame work)
    (closed : queue.ParentRegistryClosed parents) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).ParentLinksComplete parents :=
  (ParentLinkFrame.replayGraphEvents ⟨unique, registration, closed, complete⟩
    events matching canonical available).complete

/-- Complete canonical parent links survive actual normalized replay of matched batches.
Witness: replay the concrete registration package through each batch; publisher normalization
changes neither group records nor permanent registration. Empty or ignored batches are allowed.
-/
theorem State.ParentLinksComplete.runNormalized {queue : State} {work parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (_live : queue.LiveGroupsRegistered) (_tasks : queue.TaskGroupsRegistered)
    (registration : queue.RegistrationFrame work)
    (closed : queue.ParentRegistryClosed parents) (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.runNormalized batches).1.ParentLinksComplete parents := by
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (current : State) (frame : ParentLinkFrame current work parents)
      : ParentLinkFrame
          (more.foldl (fun next batch => (next.handleGraphEvents batch).1) current) work parents := by
    induction more generalizing current with
    | nil => exact frame
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.handleGraphEvents batch (matching batch (included List.mem_cons_self)) canonical)
  rw [State.runNormalized_stateFold]
  exact (loop batches (fun _ member => member) queue
    ⟨unique, registration, closed, complete⟩).complete

/-- Source-assigned parents remain fully linked throughout valid normalized replay.
Witness: exact canonical lowering establishes initial links; source matching preserves them.
The assignment is explicit so callers can share it with other generated-work certificates.
-/
theorem createWorkQueue_runNormalized_parentLinksComplete {work : Execution.Work}
    {parents} (certified : DeclarationCoverage.Certified [] work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.ParentLinksComplete
        parents := by
  have registered := createWorkQueue_registration work certified
  exact (createWorkQueue_parentLinksComplete (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
    ).runNormalized (createWorkQueue_groupRefsUnique _) registered.1 registered.2 (State.initialize_registrationFrame certified)
    (createWorkQueue_parentRegistryClosed canonical certified) batches
    (fun _ batch _ event => valid.eachMatches (List.mem_flatten.mpr ⟨_, batch, event⟩)) canonical

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
