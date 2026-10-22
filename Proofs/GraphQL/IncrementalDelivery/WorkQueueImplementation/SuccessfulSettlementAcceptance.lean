import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureSettlements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedLookupPreservation

/-! Contributors to healthy successful closures cannot have had their successes ignored. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The fresh source success must take the actual storing branch of its handler
-----------------------------------------------------------------------------------------

/-- An admitted successful task input has a present task node.
Witness: source start acceptance is exactly task presence. No contributor health guard
is evaluated by the success handler.
-/
theorem ExecutedWork.replayGraphEvents_success_present
    {work before occurrence result}
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch
          (before ++ [.taskSuccess occurrence result])
        = true)
    : ∃ node,
        ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          occurrence
        = some node := by
  have accepted := State.acceptsBatch_atPrefix (State.initialize (Work.fromExecution work))
    before (.taskSuccess occurrence result) [] started
  cases found
        : ((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).taskNode?
            occurrence with
  | none => simp only [State.acceptsGraphEvent, found, Option.isSome_none,
      Bool.false_eq_true] at accepted
  | some node => exact ⟨node, rfl⟩

-----------------------------------------------------------------------------------------
-- Actual successful closure provides durable source-ledger health at each earlier input
-----------------------------------------------------------------------------------------

/-- A successful group carrier excludes invalidation from all preceding source failures.
Witness: its actual retirement is healthy in the accepted contribution inventory, and
generated valid started replay equates that inventory's invalidation closure with the
full source ledger. The two ledgers need not contain the same failure tokens.
-/
theorem ExecutedWork.successfulCarrier_sourceOwnerHealthy
    {work before event group groups streams} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    : ¬GroupInvalidated work (GraphEvent.failureSettlements (before ++ [event]))
        group.ref := by
  obtain ⟨_, _, _, healthy, _⟩ := generated.replayGraphEvents_successfulCarrier_retiredHealthy
    valid (State.acceptsBatch_prefix started) carrier
  intro invalid
  exact healthy ((generated.failureInventories_groupInvalidated_iff _ valid started
    group.ref).mp invalid).toRecordInvalidated

/-- Any successful input contributing to a later successful carrier was actually processed.
Witness: source-prefix freshness/start laws and monotone failure health allow the complete
guard theorem at that exact input boundary. This rules out ignored success, but does not
yet assert that its installed value survives or publishes before the later carrier.
-/
theorem ExecutedWork.successfulCarrier_contributorSuccess_accepted
    {work before event group groups streams earlier occurrence result owners producer
      payload}
    (_generated : ExecutedWork work) (_valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (_carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (prior : (earlier ++ [.taskSuccess occurrence result]).IsPrefix (before ++ [event]))
    (_known : TaskAt work occurrence owners producer payload)
    (_contributes : group.ref ∈ owners)
    : ∃ node,
        ((State.initialize (Work.fromExecution work)).replayGraphEvents earlier).taskNode?
          occurrence
        = some node := by
  have starts : (State.initialize (Work.fromExecution work)).acceptsBatch
      (earlier ++ [.taskSuccess occurrence result]) = true := by
    obtain ⟨later, same⟩ := prior
    apply State.acceptsBatch_prefix (after := later)
    rwa [same]
  exact ExecutedWork.replayGraphEvents_success_present starts

-----------------------------------------------------------------------------------------
-- Structural registration plus closure accounting recovers an actual storing boundary
-----------------------------------------------------------------------------------------

/-- Every registered contributor to a successful carrier has an earlier storing boundary.
Witness: closure settlement accounting supplies a success input, permanent registry
provenance identifies its owner set, and the healthy-carrier theorem rules out rejection
at that input. The boundary may be the carrier's own handler or an earlier handler.
-/
theorem ExecutedWork.successfulCarrier_registeredContributor_processed
    {work before event group groups streams task} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (registered
      : task
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            (before ++ [event])).tasks)
    (contributes : group.ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : ∃ earlier result later node,
        before ++ [event] = earlier ++ .taskSuccess task.occurrence result :: later
        ∧ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            earlier).taskNode?
            task.occurrence
          = some node := by
  obtain ⟨result, supplied⟩ := generated.successfulCarrier_registeredContributor_succeeded
    valid started carrier registered contributes
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp supplied
  have accounting := (createWorkQueue_pendingAccounting work).replayGraphEvents (before := [])
    generated (before ++ [event]) valid started
  obtain ⟨_, payload, producer, _, known⟩ := (accounting.matching task registered).1
  have prior : (earlier ++ [GraphEvent.taskSuccess task.occurrence result]).IsPrefix
      (before ++ [event]) :=
    ⟨later, by simpa only [List.append_assoc, List.singleton_append] using split.symm⟩
  obtain ⟨node, found⟩ := generated.successfulCarrier_contributorSuccess_accepted
    valid started carrier prior known contributes
  exact ⟨earlier, result, later, node, split, found⟩

/-- Every root structural contributor to a successful carrier has actually been processed.
Witness: inverse root lowering supplies registration unconditionally, then the general
registered-contributor theorem recovers its real successful source handler and guard.
-/
theorem ExecutedWork.successfulCarrier_rootContributor_processed
    {work before event group groups streams address owners payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (known : TaskAt work (.executionGroup address) owners none payload)
    (contributes : group.ref ∈ owners)
    : ∃ earlier result later node,
        before ++ [event]
          = earlier ++ .taskSuccess (.executionGroup address) result :: later
        ∧ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            earlier).taskNode?
            (.executionGroup address)
          = some node := by
  obtain ⟨task, registered, occurrence, groups⟩ :=
    TaskAt.executionGroup_replay_registered known (before ++ [event])
  simpa only [occurrence] using generated.successfulCarrier_registeredContributor_processed
    valid started carrier registered (groups.symm ▸ contributes)

/-- Registered successful contributors really enter a prepared buffer before release.
Witness: recover their accepted success boundary and apply exact storage/integration
lookup preservation. Subsequent publication, retention, or cancellation is a separate
obligation; this does not infer any of them from eventual lookup absence.
-/
theorem ExecutedWork.successfulCarrier_registeredContributor_prepared
    {work before event group groups streams task} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (registered
      : task
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            (before ++ [event])).tasks)
    (contributes : group.ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : ∃ earlier result later node buffered,
        before ++ [event] = earlier ++ .taskSuccess task.occurrence result :: later
        ∧ (let queue :=
              (State.initialize (Work.fromExecution work)).replayGraphEvents earlier;
            queue.taskNode? task.occurrence = some node
            ∧ ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some task.occurrence)).1.taskNode?
                task.occurrence
              = some buffered
            ∧ buffered.task = node.task
            ∧ buffered.value = some result.value) := by
  obtain ⟨earlier, result, later, node, split, found⟩ :=
    generated.successfulCarrier_registeredContributor_processed valid started carrier
      registered contributes
  obtain ⟨buffered, installed, taskSame, value⟩ := State.taskSuccess_prepared_value found result
  exact ⟨earlier, result, later, node, buffered, split, found, installed, taskSame, value⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
