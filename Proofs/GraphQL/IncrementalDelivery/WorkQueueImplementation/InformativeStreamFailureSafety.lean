import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeObjectFailureSafety

/-! Actual failed stream actions are licensed on the same informative mixed cut list. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Source readiness supplies the unique generated stream producer's earlier success. -/
theorem GraphEvent.Ready.streamProducer_succeeded_fromReady
    {work stream dependencies producer closing}
    {before : List GraphEvent} {event : GraphEvent}
    (ready : event.Ready work before) (generated : ExecutedWork work)
    (action : event.streamAction = some (stream.ref, closing))
    (known : NodeAt work stream .stream dependencies producer)
    : ∀ source,
        producer = some source → source ∈ before.flatMap GraphEvent.successes := by
  cases event with
  | taskSuccess | taskFailure | groupFailure => cases action
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

/-- Each actual failed stream item is uncancelled under its informative mixed predecessors.
Witness: unique stream closure excludes earlier item causes; selected object causes remain
inside the actual source prefix. Earlier successful-item safety protects the producer and
the source's healthy release dependency.
-/
theorem informativeStreamFailures_uncancelled {work inputs w streams}
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
            (informativeObjectFailureCuts work
              (queue.sourceRunBlocks publisher inputs).2.2)
            streams)
    : ∀ before cut address ordinal after,
        w.failures = before ++ (cut, .item address ordinal) :: after
        → ¬TaskCancelled work w.matching (w.events.take cut) before
            (.item address ordinal) := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := informativeObjectFailureCuts work
    (queue.sourceRunBlocks publisher inputs).2.2
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
        createWorkQueue_informativeObjectFailureCuts_origin generated valid _ object
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
  obtain ⟨received, input, later, sourceSplit, action, actualCut, _ledger, _⟩ :=
    createWorkQueue_atomicStream_sourcePrefix valid started selected rfl
  have sourcePrefix : (received ++ [input]).IsPrefix inputs.flatten :=
    ⟨later, by simp [sourceSplit, List.append_assoc]⟩
  have prior : received.IsPrefix inputs.flatten := ⟨input :: later, sourceSplit.symm⟩
  have localLaws := valid.atPrefix sourcePrefix
  have producerSucceeded := GraphEvent.Ready.streamProducer_succeeded_fromReady
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
          have health := generated.activeObjectStreamHealthy_atSourceCut valid started
            located action actualCut failedPayloads
            (fun occurrence owners producer path result descriptor member => ?_)
            earlierSafe contributors
          · exact task_uncancelled_of_successfulProducerSafety known List.mem_cons_self health.2
              failedPayloads succeeded (by intro parent same; cases same; exact health.1)
          · have full := failedBefore_mono included (w.events.take cut).length member
            have atCut := failedBefore_subset w.failures (List.length_take_le _ _) full
            have objectMember := (cuts.object_mem_iff partition descriptor).mp atCut
            obtain ⟨entry, selected, same⟩ := List.mem_map.mp objectMember
            have available := (informativeObjectFailureCuts_sublist work _).subset
              (List.mem_filter.mp selected).1
            obtain ⟨errors, received⟩ := createWorkQueue_availableObjectFailureCuts_source generated valid available
            rw [same] at received
            exact List.mem_reverse.mpr (List.mem_flatMap.mpr ⟨_, received, List.mem_cons_self⟩)

/-- Successful-item safety licenses the entire informative failure inventory.
Witness: the same announced cut list and matching are used by both occurrence cases;
neither runtime failure-origin metadata nor an additional source law is introduced.
-/
theorem informativeFailureWitness {work inputs w streams}
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
            (informativeObjectFailureCuts work
              (queue.sourceRunBlocks publisher inputs).2.2)
            streams)
    : FailureWitness work (initialRefs work) w.matching w.events w.failures := by
  apply failureWitness announced
  intro before cut occurrence after split
  cases occurrence with
  | executionGroup address =>
      exact informativeObjectFailures_uncancelled generated valid started announced safe
        cuts exactCuts before cut address after split
  | item address ordinal =>
      exact informativeStreamFailures_uncancelled generated valid started announced safe
        cuts exactCuts before cut address ordinal after split

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
