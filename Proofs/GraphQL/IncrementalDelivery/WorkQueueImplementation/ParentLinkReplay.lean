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
private structure ParentLinkFrame (queue : State) (parents : Nat → Keys) : Prop where
  unique : queue.GroupKeysUnique
  live : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  closed : queue.ParentRegistryClosed parents
  complete : queue.ParentLinksComplete parents

/-- One matched source event preserves the whole concrete registration package.
Witness: independent key/registry preservation plus complete-link handler preservation.
-/
private theorem ParentLinkFrame.handleGraphEvent {queue : State} {work parents}
    (frame : ParentLinkFrame queue parents) (event : GraphEvent)
    (matching : event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : ParentLinkFrame (queue.handleGraphEvent event).1 parents := by
  have registered := queue.handleGraphEvent_registration frame.live frame.tasks event matching
  exact ⟨frame.unique.handleGraphEvent event, registered.1, registered.2.1,
    frame.closed.handleGraphEvent frame.live frame.tasks event matching canonical,
    frame.complete.handleGraphEvent frame.unique frame.live frame.tasks frame.closed
      event matching canonical⟩

/-- Raw event replay preserves complete links and registration prerequisites together.
Witness: induction over the actual executable state fold, not an assumed abstract run.
-/
private theorem ParentLinkFrame.replayGraphEvents {queue : State} {work parents}
    (frame : ParentLinkFrame queue parents) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : ParentLinkFrame (queue.replayGraphEvents events) parents := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      exact ih (frame.handleGraphEvent event (matching event List.mem_cons_self) canonical)
        (fun next member => matching next (List.mem_cons_of_mem _ member))

/-- Batch handling preserves the package, including skipped and terminal branches.
Witness: raw handler induction; output accumulation and the final done flag are irrelevant
to the group-node map and permanent registration fields.
-/
private theorem ParentLinkFrame.handleGraphEvents {queue : State} {work parents}
    (frame : ParentLinkFrame queue parents) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : ParentLinkFrame (queue.handleGraphEvents events).1 parents := by
  unfold State.handleGraphEvents
  split
  · exact frame
  · have replayed := frame.replayGraphEvents events matching canonical
    dsimp only
    rw [State.foldGraphEvents_state]
    split
    · exact ⟨replayed.unique, replayed.live, replayed.tasks, replayed.closed, replayed.complete⟩
    · exact replayed

-----------------------------------------------------------------------------------------
-- The generated source assignment supplies the certificate at every real replay boundary
-----------------------------------------------------------------------------------------

/-- Complete canonical parent links survive every prefix of matched raw source events.
Witness: the concrete registration frame induction, without source start or output admission.
-/
theorem State.ParentLinksComplete.replayGraphEvents {queue : State} {work parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupKeysUnique)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.replayGraphEvents events).ParentLinksComplete parents :=
  (ParentLinkFrame.replayGraphEvents ⟨unique, live, tasks, closed, complete⟩
    events matching canonical).complete

/-- Complete canonical parent links survive actual normalized replay of matched batches.
Witness: replay the concrete registration package through each batch; publisher normalization
changes neither group records nor permanent registration. Empty or ignored batches are allowed.
-/
theorem State.ParentLinksComplete.runNormalized {queue : State} {work parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupKeysUnique)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : (queue.runNormalized batches).1.ParentLinksComplete parents := by
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (current : State) (frame : ParentLinkFrame current parents)
      : ParentLinkFrame
          (more.foldl (fun next batch => (next.handleGraphEvents batch).1) current) parents := by
    induction more generalizing current with
    | nil => exact frame
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.handleGraphEvents batch (matching batch (included List.mem_cons_self)) canonical)
  rw [State.runNormalized_stateFold]
  exact (loop batches (fun _ member => member) queue
    ⟨unique, live, tasks, closed, complete⟩).complete

/-- Source-assigned parents remain fully linked throughout valid normalized replay.
Witness: exact canonical lowering establishes initial links; source matching preserves them.
The assignment is explicit so callers can share it with other generated-work certificates.
-/
theorem createWorkQueue_runNormalized_parentLinksComplete {work : Execution.Work}
    {parents}
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.ParentLinksComplete
        parents := by
  have registered := createWorkQueue_registration work
  exact (createWorkQueue_parentLinksComplete (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
    ).runNormalized (createWorkQueue_groupKeysUnique _) registered.1 registered.2
    (createWorkQueue_parentRegistryClosed canonical) batches
    (fun _ batch _ event => valid.eachMatches (List.mem_flatten.mpr ⟨_, batch, event⟩)) canonical

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
