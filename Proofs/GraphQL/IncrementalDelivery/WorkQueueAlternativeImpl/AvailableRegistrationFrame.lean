import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationReceiptCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerHandlers

/-! Registration frames at actual cache-aware preparation cuts. Enlarged exclusion sets
are proof evidence for unfinished tasks, not runtime settlement histories or cause caches.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

/-- A larger exclusion set weakens pending lower bounds and remaining link obligations.
The original consumed ledger is retained separately when processing the next outcome.
-/
theorem pendingAccounting_weakenSettled {queue work before after}
    (accounted : ReferenceWorkQueue.State.PendingAccounting queue work before)
    (included : before.Subset after)
    : queue.PendingAccounting work after :=
  ⟨
    accounted.pending.weakenSettled included,
    accounted.links.weaken included,
    accounted.refs,
    accounted.memberships,
    accounted.liveGroups,
    accounted.taskGroups,
    accounted.sound,
    accounted.matching,
    accounted.started,
    accounted.registration
  ⟩

/-- An all-outcomes ledger supplies the independent registration frame. -/
theorem SourceRegistrationFrame.of_pendingAccounting {queue work settled}
    (accounted : ReferenceWorkQueue.State.PendingAccounting queue work settled)
    : SourceRegistrationFrame queue settled work :=
  ⟨
    ⟨accounted.refs, accounted.liveGroups, accounted.taskGroups, accounted.links⟩,
    accounted.matching,
    accounted.sound
  ⟩

/-- Enlarging exclusions retains every remaining unfinished-task link obligation. -/
theorem SourceRegistrationFrame.weaken {queue work before after}
    (frame : SourceRegistrationFrame queue before work) (included : before.Subset after)
    : SourceRegistrationFrame queue after work :=
  ⟨
    ⟨frame.keys, frame.live, frame.contributors, frame.links.weaken included⟩,
    frame.matching,
    frame.sound
  ⟩

/-- A registered source-matched descriptor has its exact permanent catalogue lookup. -/
theorem SourceRegistrationFrame.catalogue {queue work settled task}
    (frame : SourceRegistrationFrame queue settled work) (member : task ∈ queue.tasks)
    : ReferenceWorkQueue.State.task? queue task.occurrence = some task := by
  cases found : queue.task? task.occurrence with
  | none =>
      exact False.elim ((List.find?_eq_none.mp found task member)
        ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr rfl))
  | some canonical =>
      have same := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : ReferenceWorkQueue.Task =>
          candidate.occurrence == task.occurrence) found)
      have identical := matchedTasks_eq_of_occurrence_eq
        (frame.matching canonical (List.mem_of_find?_eq_some found))
        (frame.matching task member) same
      exact congrArg some identical

/-- All surviving started task links imply the buffered-only source obligation. -/
theorem storedTaskLinks_of_taskOwnerFrame {queue work}
    (frame : ReferenceWorkQueue.State.TaskOwnerFrame queue work)
    : queue.StoredTaskLinks :=
  ReferenceWorkQueue.State.StoredTaskLinks.of_all
    (fun _ member => frame.disposition.startedLinks frame.registered member)

/-- Source-matched registration preserves the same frame for the supplied snapshot.
Object registration precedes settlement; stream preparation includes every actual item start.
-/
theorem registrationSnapshot_frame_available {queue work settled}
    (frame : SourceRegistrationFrame queue settled work)
    (context : queue.RegistrationFrame work) (event : GraphEvent)
    (matched : event.MatchesWork work) (available : List (Occurrence × Nat))
    : SourceRegistrationFrame (registrationSnapshot queue event available) settled
        work := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [registrationSnapshot, found] using frame
      | some node =>
          let stored : State :=
            { queue := queue.putTaskNode { node with value := some result.value } }
          have installed : SourceRegistrationFrame stored.queue settled work :=
            ⟨⟨frame.keys, frame.live, frame.contributors, frame.links⟩, frame.matching, frame.sound⟩
          have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
            intro task member
            obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
            exact ⟨⟨address, payload, some occurrence, same, located⟩,
              matched.childTask_groupsExact member⟩
          simp only [registrationSnapshot, found]
          have certificate := (context.children node.task
            (context.started node (ReferenceWorkQueue.State.taskNode?_some found).1)).sourceChild
              (ReferenceWorkQueue.State.taskNode?_some found).2 matched
          exact installed.integrate result.work certificate.contributors known
            (some occurrence)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using frame
      | true =>
          simp only [registrationSnapshot, active, ↓reduceIte]
          have loop (more : List ReferenceWorkQueue.StreamItem) (included : more.Subset items)
              (acc : StreamRegistrationAcc)
              (prior : SourceRegistrationFrame acc.1.queue settled work)
              : SourceRegistrationFrame
                  (more.foldl (fun acc item => streamRegistrationStep acc item available)
                    acc).1.queue settled work := by
            induction more generalizing acc with
            | nil => exact prior
            | cons item rest ih =>
                have member := included List.mem_cons_self
                have known : ∀ task ∈ item.work.tasks,
                    ReferenceWorkQueue.TaskMatches work task := by
                  intro task supplied
                  obtain ⟨address, payload, same, located⟩ :=
                    matched.streamItem_childTask_producer member supplied
                  exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
                    matched.streamItem_childTask_groupsExact member supplied⟩
                exact ih (fun _ member => included (List.mem_cons_of_mem _ member))
                  (streamRegistrationStep acc item available)
                  (streamRegistrationStep_frame prior item
                    (matched.streamItem_childTasksCovered context.source member) known
                    available)
          exact loop items (List.Subset.refl _) _ frame
  | taskFailure | groupFailure | streamSuccess | streamFailure => exact frame

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
