import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTaskRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionSettlement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay

/-! Actual source replay derives rejection retention against successful counter settlements. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A fixed successful task cannot occur in a valid source prefix's object failures. -/
theorem ValidGraphEvents.succeeds_not_failureSettlements {work events occurrence}
    (valid : ValidGraphEvents work events) (succeeds : TaskSucceeds work occurrence)
    : occurrence ∉ GraphEvent.failureSettlements events := by
  intro recorded
  obtain ⟨owners, producer, path, errors, known⟩ :=
    valid.failureSettlements_known occurrence recorded
  obtain ⟨otherOwners, birth, payload, descriptor, successful⟩ := succeeds
  have same := (known.unique descriptor).2.2
  subst payload
  simp [Payload.failure] at successful

/-- Each object success in a valid source prefix has a successful fixed task outcome. -/
theorem ValidGraphEvents.groupSettlements_succeed {work events occurrence}
    (valid : ValidGraphEvents work events)
    (member : occurrence ∈ GraphEvent.groupSettlements events)
    : TaskSucceeds work occurrence := by
  have recorded : occurrence ∈ events.flatMap GraphEvent.groupSuccesses :=
    List.mem_reverse.mp member
  obtain ⟨event, eventMember, success⟩ := List.mem_flatMap.mp recorded
  have succeeds : occurrence ∈ event.successes := by
    cases event <;> simp_all [GraphEvent.groupSuccesses, GraphEvent.successes]
  exact valid.successes_succeed (List.mem_flatMap.mpr ⟨event, eventMember, succeeds⟩)

/-- Every accepted FIFO step retains earlier failed tasks at surviving owners.
The consumed failure inventory advances at notification time; earlier cache exposure
preserves it without claiming that every available failure has already been consumed.
-/
theorem State.RetainedFailures.handleGraphEvent_ofDisposition {queue : State}
    {work before failed} (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before)) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat) := [])
    (evidence
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    : (queue.handleGraphEvent event available).1.RetainedFailures work
        (event.groupFailures ++ failed) := by
  let current := queue.cacheTaskFailures available
  have cached := prior.cacheTaskFailures available
  have counted := ledger.cacheTaskFailures available
  have disjoint : ∀ task ∈ GraphEvent.groupSettlements before, task ∉ failed := by
    intro task member recorded
    exact valid.succeeds_not_failureSettlements (valid.groupSettlements_succeed member)
      (included recorded)
  cases event with
  | taskSuccess occurrence result =>
      cases found : current.taskNode? occurrence with
      | none =>
          change (current.taskSuccess occurrence result available).1.RetainedFailures work failed
          simpa only [State.taskSuccess, found] using cached
      | some node =>
          apply cached.taskSuccess counted occurrence result node found
            (available := available)
          · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
              (GraphEvent.groupSettlements_subsetIdentities before member)
          · exact fun member => valid.succeeds_not_failureSettlements
              (source.successes_succeed (by simp [GraphEvent.successes])) (included member)
          · exact disjoint
          · exact counted.matching.contributorsNodup generated
              (counted.started node (List.mem_of_find?_eq_some found))
          · intro task member
            obtain ⟨address, payload, same, known⟩ := source.childTask_producer member
            exact ⟨⟨address, payload, some occurrence, same, known⟩,
              source.childTask_groupsExact member⟩
  | taskFailure occurrence errors =>
      cases found : current.taskNode? occurrence with
      | none =>
          change (current.taskFailure occurrence errors).1.RetainedFailures work
            (occurrence :: failed)
          simp only [State.taskFailure, found]
          have absent :=
            ((evidence occurrence errors rfl).1.cacheTaskFailures available).absent found
          obtain ⟨task, registered, identity⟩ := (evidence occurrence errors rfl).2
          have member : task ∈ current.tasks := by
            simpa only [current, State.cacheTaskFailures_tasks] using registered
          obtain ⟨_, _, _, _, descriptor⟩ := (counted.matching task member).1
          rw [identity] at descriptor
          have pending : task.occurrence ∉ GraphEvent.groupSettlements before := by
            rw [identity]
            intro prior
            exact fresh.2.2.1 occurrence List.mem_cons_self
              (GraphEvent.groupSettlements_subsetIdentities before prior)
          refine ⟨?_, ?_⟩
          · intro other recorded owners known group live contributes
            rcases List.mem_cons.mp recorded with same | old
            · subst other
              obtain ⟨producer, payload, otherKnown⟩ := known
              have sameOwners := (descriptor.unique otherKnown).1
              have linked := counted.links task member pending group live
                (sameOwners.symm ▸ contributes)
              exact (absent group live (identity ▸ linked)).elim
            · exact cached.retained other old owners known group live contributes
          · intro ref unregistered other recorded owners known contributes
            rcases List.mem_cons.mp recorded with same | old
            · subst other
              obtain ⟨producer, payload, otherKnown⟩ := known
              have sameOwners := (descriptor.unique otherKnown).1
              exact unregistered (counted.taskGroups task member ref
                (sameOwners.symm ▸ contributes))
            · exact cached.fresh ref unregistered other old owners known contributes
      | some node =>
          exact cached.taskFailure counted occurrence errors node found
            (fun member =>
              fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                (GraphEvent.groupSettlements_subsetIdentities before member)) source
  | streamItems stream items =>
      exact cached.streamItems counted.refs counted.sound counted.matching source
        counted.pending disjoint available
  | streamSuccess stream =>
      change (current.streamSuccess stream).1.RetainedFailures work failed
      unfold State.streamSuccess
      split <;> exact cached
  | streamFailure stream errors =>
      change (current.streamFailure stream errors).1.RetainedFailures work failed
      unfold State.streamFailure
      split <;> exact cached

  | groupFailure notice =>
      change (current.groupFailure notice).1.RetainedFailures work failed
      unfold State.groupFailure
      split
      · exact cached
      · split
        · exact ⟨cached.retained, cached.fresh⟩
        · exact cached

/-- The live-callback specialization of rejection retention. -/
theorem State.RetainedFailures.handleGraphEvent {queue : State} {work before failed}
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (event : GraphEvent) (source : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.RetainedFailures work
        (event.groupFailures ++ failed) := by
  apply prior.handleGraphEvent_ofDisposition ledger generated valid included event
    source fresh available
  intro occurrence errors same
  subst event
  cases found : queue.taskNode? occurrence with
  | none => simp [State.acceptsGraphEvent, found] at accepted
  | some node =>
      exact ⟨.inl ⟨node, found⟩, node.task,
        ledger.started node (List.mem_of_find?_eq_some found), (State.taskNode?_some found).2⟩

/-- Enqueuing internal notices preserves rejection retention. -/
theorem State.RetainedFailures.dispatchGraphEvent_ofDisposition {queue : State}
    {work before failed} (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before)) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat) := [])
    (evidence
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    : (queue.dispatchGraphEvent event available).1.RetainedFailures work
        (event.groupFailures ++ failed) := by
  have next := prior.handleGraphEvent_ofDisposition ledger generated valid included event source fresh available evidence
  exact ⟨next.retained, next.fresh⟩

/-- Enqueuing internal notices preserves rejection retention. -/
theorem State.RetainedFailures.dispatchGraphEvent {queue : State} {work before failed}
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (event : GraphEvent) (source : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.RetainedFailures work
        (event.groupFailures ++ failed) := by
  have next := prior.handleGraphEvent ledger generated valid included event source fresh accepted available
  exact ⟨next.retained, next.fresh⟩

/-- Within-batch replay retains consumed failures under one fixed cache snapshot. -/
theorem State.RetainedFailures.replayGraphEvents {queue : State}
    {work before failed available} (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.eventsStarted available queue events = true)
    : (queue.replayGraphEvents events available).RetainedFailures work
        (GraphEvent.failureSettlements events ++ failed) := by
  induction events generalizing queue before failed with
  | nil => simpa [State.replayGraphEvents, GraphEvent.failureSettlements] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      obtain ⟨validBefore, source, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have nextRetained := prior.dispatchGraphEvent ledger generated validBefore included event
        source fresh accepts.1 available
      have nextLedger := ledger.dispatchGraphEvent_successes_ofMatching generated
        (GraphEvent.groupSettlements_subsetIdentities before) event source fresh available
      rw [← GraphEvent.groupSettlements_append] at nextLedger
      have nextIncluded : (event.groupFailures ++ failed).Subset
          (GraphEvent.failureSettlements (before ++ [event])) := by
        rw [GraphEvent.failureSettlements_append]
        intro task member
        rcases List.mem_append.mp member with member | member
        · exact List.mem_append_left _ member
        · exact List.mem_append_right _ (included member)
      have result := ih nextRetained nextLedger nextIncluded
        (by simpa [List.append_assoc] using valid) accepts.2
      simpa only [State.replayGraphEvents, GraphEvent.failureSettlements_cons,
        List.append_assoc, List.foldl_cons]
        using result

/-- Initialization has no failed task inventory. -/
theorem createWorkQueue_retainedFailures (input : Work) (work : Execution.Work)
    : (State.initialize input).RetainedFailures work [] :=
  State.RetainedFailures.nil _ _

/-- Public batch admission retains rejection facts even when notification becomes stale.
Initial task eligibility supplies both its permanent descriptor and retirement evidence.
-/
theorem State.RetainedFailures.replayGraphEvents_admitted {queue : State}
    {work before failed available} (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    : (queue.replayGraphEvents events available).RetainedFailures work
        (GraphEvent.failureSettlements events ++ failed) := by
  have includedAt (fifo : List GraphEvent) :
      (GraphEvent.failureSettlements fifo ++ failed).Subset
        (GraphEvent.failureSettlements (before ++ fifo)) := by
    rw [GraphEvent.failureSettlements_append_list]
    intro occurrence member
    rcases List.mem_append.mp member with recent | old
    · exact List.mem_append_left _ recent
    · exact List.mem_append_right _ (included old)
  have result : (queue.replayGraphEvents events available).RetainedFailures work
        (GraphEvent.failureSettlements events ++ failed)
      ∧ (queue.replayGraphEvents events available).PendingAccounting work
        (GraphEvent.groupSettlements (before ++ events)) := by
    apply prefix_invariant events (fun fifo =>
      (queue.replayGraphEvents fifo available).RetainedFailures work
          (GraphEvent.failureSettlements fifo ++ failed)
        ∧ (queue.replayGraphEvents fifo available).PendingAccounting work
          (GraphEvent.groupSettlements (before ++ fifo)))
    · simpa only [State.replayGraphEvents, List.foldl_nil, GraphEvent.failureSettlements,
        List.flatMap_nil, List.reverse_nil, List.nil_append, List.append_nil] using And.intro prior ledger
    · intro fifo event rest split past
      have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
        ⟨rest, by simp [split, List.append_assoc]⟩
      obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix boundary)
      obtain ⟨retained, counted⟩ := past fifo (List.prefix_refl _)
      have evidence : ∀ occurrence errors, event = .taskFailure occurrence errors
          → (queue.replayGraphEvents fifo available).StartedTaskDisposition occurrence
            ∧ ∃ task ∈ (queue.replayGraphEvents fifo available).tasks,
                task.occurrence = occurrence := by
        intro occurrence errors same
        subst event
        obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
          (.taskFailure occurrence errors) available accepted ⟨rest, by simp [split]⟩
        have frame := (past seen seenPrefix).2
        cases found : (queue.replayGraphEvents seen available).taskNode? occurrence with
        | none =>
            simp only [State.acceptsGraphEvent, found, Option.isSome_none, Bool.false_eq_true]
              at eligible
        | some node =>
            obtain ⟨remaining, history⟩ := seenPrefix
            have validSeen : ValidGraphEvents work (before ++ seen) :=
              validBefore.prefix ⟨remaining, by simp [history, List.append_assoc]⟩
            have source := queue.replayGraphEvents_producerOrder ready ordered seen validSeen available
            have disposition := frame.startedTaskDisposition_atPrefix found source.1 source.2
              remaining (by simpa [history, List.append_assoc] using validBefore) available
            rw [← history, State.replayGraphEvents_append queue seen remaining available]
            exact ⟨
              disposition,
              node.task,
              (queue.replayGraphEvents seen available).replayGraphEvents_tasks_subset
                remaining available
                (frame.started node (List.mem_of_find?_eq_some found)),
              (State.taskNode?_some found).2
            ⟩
      have next := retained.dispatchGraphEvent_ofDisposition counted generated validBefore
        (includedAt fifo) event matching fresh available evidence
      have nextLedger := counted.dispatchGraphEvent_successes_ofMatching generated
        (GraphEvent.groupSettlements_subsetIdentities (before ++ fifo)) event matching fresh available
      rw [← GraphEvent.groupSettlements_append] at nextLedger
      constructor
      · simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil,
          GraphEvent.failureSettlements_append, List.append_assoc] using next
      · simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc] using nextLedger
  exact result.1

/-- A complete batch retains every consumed source rejection on surviving owners. -/
theorem State.RetainedFailures.handleGraphEvents {queue : State} {work before failed}
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.RetainedFailures work
        (GraphEvent.failureSettlements events ++ failed) := by
  have replayed := prior.replayGraphEvents_admitted ledger ready ordered generated
    included events valid accepted
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed

/-- Actual batch replay retains failures at their source notification boundaries. -/
theorem State.RetainedFailures.runNormalized {queue : State} {work before failed}
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.RetainedFailures work
        (GraphEvent.failureSettlements batches.flatten ++ failed) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before failed with
  | nil => simpa [State.replayBatches, GraphEvent.failureSettlements] using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := prior.handleGraphEvents ledger ready ordered generated included batch
        (valid.prefix earlier)
        running accepted
      have nextLedger := ledger.handleGraphEvents_successes generated batch (valid.prefix earlier)
        running accepted
      have nextIncluded : (GraphEvent.failureSettlements batch ++ failed).Subset
          (GraphEvent.failureSettlements (before ++ batch)) := by
        rw [GraphEvent.failureSettlements_append_list]
        intro task member
        rcases List.mem_append.mp member with member | member
        · exact List.mem_append_left _ member
        · exact List.mem_append_right _ (included member)
      have source := State.handleGraphEvents_producerOrder ready ordered batch
        (valid.prefix earlier) running
      have result := ih next nextLedger source.1 source.2 nextIncluded
        (by simpa [List.append_assoc] using valid) restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        GraphEvent.failureSettlements_append_list, List.append_assoc]
        using result

/-- Every valid started batch replay retains consumed failures at surviving contributors.
Retention and fresh-ref exclusion are internal facts; causal cut licensing is separate.
-/
theorem ExecutedWork.runNormalized_retainedFailures {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.RetainedFailures
        work (GraphEvent.failureSettlements batches.flatten) := by
  have result := (createWorkQueue_retainedFailures (Work.fromExecution work) work).runNormalized
    (createWorkQueue_pendingAccounting work generated.declarations) (createWorkQueue_producerOrder work).1
    (createWorkQueue_producerOrder work).2 generated (before := [])
    (by intro task member; cases member) batches valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)
  simpa only [List.append_nil] using result

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
