import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectFailureSafety

/-! Failed stream items are safe before their own cut in the common mixed inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A ready stream action has already received its structural producer's success.
Witness: invert source readiness and identify the generated stream's unique producer
using its action ref. The item payload is not used to select a producer occurrence.
-/
theorem GraphEvent.Ready.streamProducer_succeeded
    {work stream dependencies producer closing}
    {before : List GraphEvent} {event : GraphEvent}
    (ready : event.Ready work before) (generated : ExecutedWork work)
    (action : event.streamAction = some (stream.ref, closing))
    (known : NodeAt work stream .stream dependencies producer)
    : ∀ source,
        producer = some source → source ∈ before.flatMap GraphEvent.successes := by
  cases event with
  | taskSuccess | taskFailure => cases action
  | streamItems node items =>
      obtain ⟨_, _, _, _, located, _, _, supported, _⟩ := ready
      have refEq := (Prod.mk.inj (Option.some.inj action)).1
      have same := generated.streamProducer_unique (.stream located) known refEq
      intro source produced
      exact supported source (same.trans produced)
  | streamSuccess node | streamFailure node errors =>
      obtain ⟨_, _, _, _, located, supported, _⟩ := ready
      have refEq := (Prod.mk.inj (Option.some.inj action)).1
      have same := generated.streamProducer_unique (.stream located) known refEq
      intro source produced
      exact supported source (same.trans produced)

namespace ConformancePlan

/-- Every failed stream item in `w` is uncancelled under its ordered predecessors.
This is the item-task part of `UncancelledFailures`; the current failure is excluded,
but every earlier cut, including an equal-index object settlement, remains visible.
-/
def StreamFailuresSafe (work : Execution.Work) (w : Witness) : Prop :=
  ∀ before cut address ordinal after,
    w.failures = before ++ (cut, .item address ordinal) :: after
    → ¬TaskCancelled work w.matching (w.events.take cut) before (.item address ordinal)

-----------------------------------------------------------------------------------------
-- Failed actions use their predecessor cuts, not the nonfailure publication theorem
-----------------------------------------------------------------------------------------

/-- General item safety also licenses stream failures on the same ordered inventory.
Witness: the actual failed action recovers its active pre-handler state. Unique stream
closure excludes earlier direct failure; root/item producers are already safe, while
object producers retain a healthy release owner. Visible object cuts align with the
earlier source ledger. The current failing item is never assumed safe or published.
-/
theorem streamFailuresSafe_of_successfulItems {work inputs w streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = mergeFailureCuts
            (sourceObjectFailureCuts 0
              (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2))
            streams)
    : StreamFailuresSafe work w := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
  have partition : w.failures.Perm (streams ++ objects) :=
    exactCuts ▸ mergeFailureCuts_partition objects streams
  intro before cut address ordinal after split
  have included : before.Subset w.failures := by
    rw [split]
    exact List.subset_append_left _ _
  have current : (cut, Occurrence.item address ordinal) ∈ w.failures := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have fromStream : (cut, Occurrence.item address ordinal) ∈ streams := by
    rcases List.mem_append.mp (partition.mem_iff.mp current) with item | object
    · exact item
    · obtain ⟨_, _, _, _, _, known, _⟩ :=
        createWorkQueue_eligibleObjectFailureCuts_origin generated valid _ object
      cases StructuralEquivalence.taskAt_of_current known
  obtain ⟨stream, errors, producer, selected, known⟩ := cuts.2 _ fromStream
  obtain ⟨_, dependencies, located⟩ := itemTask_owner_nodeAt known
  have failedPayloads : ∀ index occurrence,
      (index, occurrence) ∈ before
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true :=
    fun index occurrence member =>
      (announced.1.2.2.1 (index, occurrence) (included member)).2.2
  obtain ⟨owners, ref, ⟨parent, payload, descriptor⟩, owner, direct⟩ :=
    createWorkQueue_mixedFailureCuts_directHealthyOwner generated valid started cuts
      (exactCuts.symm.trans split)
  have ownerEq : ref = stream.ref :=
    List.mem_singleton.mp ((known.unique descriptor).1.symm ▸ owner)
  subst ref
  have contributors : ∀ occurrence owners,
      TaskHasOwners work occurrence owners → stream.ref ∈ owners
      → occurrence ∉ failedBefore before (w.events.take cut).length := by
    intro occurrence owners descriptor contributes member
    obtain ⟨entry, retained, same⟩ := List.mem_map.mp member
    exact direct occurrence owners
      (List.mem_map.mpr ⟨entry, (List.mem_filter.mp retained).1, same⟩)
      descriptor contributes
  obtain ⟨received, input, later, sourceSplit, action, accepted, ledger, _⟩ :=
    createWorkQueue_atomicStream_sourcePrefix started selected rfl
  have sourcePrefix : (received ++ [input]).IsPrefix inputs.flatten :=
    ⟨later, by simp [sourceSplit, List.append_assoc]⟩
  have prior : received.IsPrefix inputs.flatten := ⟨input :: later, sourceSplit.symm⟩
  have localLaws := valid.atPrefix sourcePrefix
  have producerSucceeded := GraphEvent.Ready.streamProducer_succeeded
    localLaws.2.2 generated action located
  have succeeded : ∀ source, producer = some source → TaskSucceeds work source :=
    fun source same => (valid.prefix prior).successes_succeed (producerSucceeded source same)
  have earlierSafe := safe.prefix prior cut included
  cases producer with
  | none =>
      have empty : dependencies = [] := by
        obtain ⟨_, _, atStream⟩ := located
        exact Correctness.located_producer_context atStream
      have healthy := generated.streamHealthy_of_producerSafety (matching := w.matching)
        failedPayloads located
        succeeded (by intro source impossible; cases impossible) contributors (.inl empty)
      exact task_uncancelled_of_successfulProducerSafety known List.mem_cons_self healthy
        failedPayloads succeeded (by intro source impossible; cases impossible)
  | some parent =>
      cases parent with
      | item source index =>
          have empty : dependencies = [] := by
            obtain ⟨_, _, atStream⟩ := located
            exact Correctness.located_producer_context atStream
          have parentSafe := earlierSafe source index (producerSucceeded _ rfl)
          have healthy := generated.streamHealthy_of_producerSafety failedPayloads located
            succeeded (by intro parent same; cases same; exact parentSafe)
            contributors (.inl empty)
          exact task_uncancelled_of_successfulProducerSafety known List.mem_cons_self
            healthy failedPayloads succeeded
            (by intro parent same; cases same; exact parentSafe)
      | executionGroup source =>
          have acceptedAll := queue.batchesStarted_acceptsBatch inputs
            (by rwa [← inputsStarted_eq_batchesStarted])
          rw [sourceSplit] at acceptedAll
          have acceptedBefore := State.acceptsBatch_prefix acceptedAll
          have active : stream.ref ∈ (queue.replayGraphEvents received).rootStreams := by
            cases input <;> simp only [GraphEvent.streamAction] at action
            all_goals try contradiction
            all_goals
              have refEq := (Prod.mk.inj (Option.some.inj action)).1
              simpa [State.acceptsGraphEvent, refEq] using accepted
          have health := generated.replayGraphEvents_activeObjectStreamHealthy_of_itemSafety
            (valid.prefix prior) acceptedBefore located active failedPayloads
            (fun occurrence owners producer path result descriptor member => ?_)
            earlierSafe contributors
          · exact task_uncancelled_of_successfulProducerSafety known List.mem_cons_self health.2
              failedPayloads succeeded (by intro parent same; cases same; exact health.1)
          · have full := failedBefore_mono included (w.events.take cut).length member
            have atCut := failedBefore_subset w.failures (List.length_take_le _ _) full
            have objectMember := (cuts.object_mem_iff partition descriptor).mp atCut
            rw [← ledger]
            exact List.mem_reverse.mpr objectMember

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
