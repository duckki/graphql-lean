import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerAvailability
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.ReleasedStreamNotices

/-! Constructive continuation after deferred work releases its remaining streams.
The hypotheses describe a reached prefix, not a stronger public scheduler contract.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Retain already accounted deferred tasks while processing streams
-----------------------------------------------------------------------------------------

/-- Every deferred occurrence in this work has published or been causally cancelled.
Stream items can remain unprocessed, including items with dynamically introduced children.
-/
def DeferredTasksAccounted (work : Work) (matching : PublicationMatching)
    (events : List WorkEvent) (failed : List Occurrence)
    : Prop :=
  ∀ address owners producer payload,
    TaskAt work (.deferred address) owners producer payload
    → Accounted work matching events failed (.deferred address)

/-- A new matched publication preserves deferred accounting. Witness: cancellation is
unchanged and every earlier publication retains its matching index.
-/
theorem DeferredTasksAccounted.publish {work matching events failed}
    (accounted : DeferredTasksAccounted work matching events failed)
    (occurrence : Occurrence) (event : WorkEvent)
    : DeferredTasksAccounted work (matchNext matching events.length occurrence)
        (events ++ [event]) failed :=
  fun address owners producer payload known =>
    (accounted address owners producer payload known).matchNext_append occurrence event

/-- Appended events and additional actual failures preserve deferred accounting.
Witness: publication-prefix preservation and causal failure monotonicity.
-/
theorem DeferredTasksAccounted.extend {work matching events failed more}
    (accounted : DeferredTasksAccounted work matching events failed)
    (included : failed ⊆ more) (tail : List WorkEvent)
    : DeferredTasksAccounted work matching (events ++ tail) more :=
  fun address owners producer payload known =>
    ((accounted address owners producer payload known).more_failures included).append tail

-----------------------------------------------------------------------------------------
-- Complete remaining stream work without changing previous observations
-----------------------------------------------------------------------------------------

/-- An explained prefix can finish once deferred tasks are accounted for, all stream
parents are closed, and produced healthy streams are announced. Witness: maximize finite
extensions retaining accounting and notice coverage; any outstanding task gives another
stream publication or failure step. Finalization then closes the remaining node keys.
-/
theorem finish_released_streams
    {paths bound work groups streams events matching failures}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (deferred : DeferredTasksAccounted work matching events (failures.map Prod.snd))
    (closed : StreamParentsCompleted work events)
    (notified
      : StreamsNotified work ((groups ++ streams).map DeliveryNode.key)
          matching events (failures.map Prod.snd))
    : ∃ tail next cuts,
        Explains work groups streams (events ++ tail) next cuts
        ∧ Terminal work ((groups ++ streams).map DeliveryNode.key) next (events ++ tail)
            (failedBefore cuts (events ++ tail).length) := by
  classical
  let property outputs next (cuts : FailureCuts) :=
    DeferredTasksAccounted work next outputs (cuts.map Prod.snd)
    ∧ StreamsNotified work ((groups ++ streams).map DeliveryNode.key) next outputs
      (cuts.map Prod.snd)
  obtain ⟨tail, next, cuts, admitted, retained, maximal⟩ :=
    explained.maximal_extension_preserving property ⟨deferred, notified⟩
  have accounted : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload
      → Accounted work next (events ++ tail) (failedBefore cuts (events ++ tail).length)
          occurrence := by
    intro occurrence owners producer payload known
    apply Classical.byContradiction
    intro outstanding
    obtain ⟨taskOccurrence, taskOwners, taskProducer, result, task, ready⟩ :=
      readyTask_exists known outstanding
    have unaccounted : ¬Accounted work next (events ++ tail)
        (failedBefore cuts (events ++ tail).length) taskOccurrence := by
      rintro (cancelled | published)
      · exact ready.2.1 cancelled
      · exact ready.1 published
    cases StructuralEquivalence.taskAt_of_current task with
    | deferred located =>
        apply unaccounted
        rw [admitted.2.1.failedBefore_eq (Nat.le_refl _)]
        exact retained.1 _ _ _ _ task
    | @item address stream items producer enclosing index outcome children located entry
      =>
        obtain ⟨key, member, healthy, uncompleted⟩ :=
          admitted.outstanding_owner task (by simp) unaccounted
        have same := List.mem_singleton.mp member
        subst key
        have streamKnown := NodeAt.stream located.toCurrent
        have opened : Open ((groups ++ streams).map DeliveryNode.key) (events ++ tail)
            stream.key := by
          refine ⟨retained.2 stream enclosing _ streamKnown ready.2.2.1 ?_, uncompleted⟩
          simpa only [admitted.2.1.failedBefore_eq (Nat.le_refl _)] using healthy
        cases outcome with
        | ok value =>
            obtain ⟨item, errors⟩ := value
            have selected := stream_owner_of_open coherent task opened healthy
            obtain ⟨newGroups, newStreams, extended, covered⟩ :=
              admitted.publish_item_streams_notified (closed.append tail) task ready selected
            have preserved := retained.1.publish (.item address index)
              (.streamValues stream [{ item, errors }] newGroups newStreams)
            have impossible := maximal
              [.streamValues stream [{ item, errors }] newGroups newStreams]
              (matchNext next (events ++ tail).length (.item address index)) cuts
              extended ⟨preserved, covered⟩
            cases impossible
        | error errors =>
            obtain ⟨owner, count, event, _, control, _, extended⟩ := admitted.failure_step
              task rfl (ready.reachable admitted task) ⟨stream.key, by simp, opened⟩
              (by simpa only [admitted.2.1.failedBefore_eq (Nat.le_refl _)] using ready.2.1)
            have noValue : ¬IsValue event := by
              rcases control with rfl | rfl <;> simp [IsValue]
            have included : cuts.map Prod.snd ⊆
                (cuts ++ [((events ++ tail).length, Occurrence.item address index)]).map
                  Prod.snd := by
              simp only [List.map_append]
              exact List.subset_append_left _ _
            have covered := retained.2.append_control noValue included
            have preserved := retained.1.extend included [event]
            have impossible := maximal [event] next
              (cuts ++ [((events ++ tail).length, .item address index)]) extended
              ⟨preserved, covered⟩
            cases impossible
  obtain ⟨closures, _, _, finished, terminal⟩ := admitted.finish_accounted accounted
  exact ⟨
    tail ++ closures,
    next,
    cuts,
    by simpa only [List.append_assoc] using finished,
    by simpa only [List.append_assoc] using terminal
  ⟩

/-- The continuation retains every previously supplied work batch and its grouping.
Witness: append singleton batches for the constructed suffix, then one termination batch.
-/
theorem released_streams_run_extension
    {paths bound work groups streams events matching failures batches}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (deferred : DeferredTasksAccounted work matching events (failures.map Prod.snd))
    (closed : StreamParentsCompleted work events)
    (notified
      : StreamsNotified work ((groups ++ streams).map DeliveryNode.key)
          matching events (failures.map Prod.snd))
    (batched : WorkBatching events batches)
    : ∃ tail : List WorkEvent,
        AdmissibleRun work
          ⟨
            groups,
            streams,
            batches ++ tail.map (fun event => [event]) ++ [[.workQueueTermination]]
          ⟩ := by
  obtain ⟨tail, next, cuts, admitted, terminal⟩ :=
    finish_released_streams coherent explained deferred closed notified
  exact ⟨tail, events ++ tail, next, cuts, admitted, terminal,
    (batched.append (WorkBatching.singletons tail)).append
      (WorkBatching.singletons [.workQueueTermination])⟩

end GraphQL.IncrementalDelivery.Correctness
