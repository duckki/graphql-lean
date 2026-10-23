import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupObjectFailureSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeStreamFailureSafety

/-! One actual startup witness licenses object and stream failure cuts jointly. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A failed stream item is uncancelled under its exact selected mixed predecessors.
Source readiness, ordered closure refs, actual release support and earlier successful-item
safety retain the same causal cuts and matching as the rest of the startup construction.
-/
theorem startup_informativeStreamFailures_uncancelled {work inputs w streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work) startup).runNormalized
              inputs).2.flatten.flatMap
            publicationAtoms)
          streams)
    (exactCuts
      : w.failures
        = mergeFailureCuts (startup.informativeObjectFailureCuts work inputs) streams)
    : ∀ before cut address ordinal after,
        w.failures = before ++ (cut, .item address ordinal) :: after
        → ¬TaskCancelled work w.matching (w.events.take cut) before
            (.item address ordinal) := by
  let objects := startup.informativeObjectFailureCuts work inputs
  have objectsKnown : ∀ entry ∈ objects, ∃ owners producer path errors,
      TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    exact startup.objectReportingCuts_objectOrigin matched generated valid entry
      ((selectObjectFailureCuts_sublist work [] _).subset member)
  have objectUnique : (objects.map Prod.snd).Nodup :=
    (reporting_metadata
      (generated.startup_objectReportingWitness startup matched valid started).1).2.sublist
      ((selectObjectFailureCuts_sublist work [] _).map Prod.snd)
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
    · obtain ⟨_, _, _, _, known⟩ := objectsKnown _ object
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
    mixedFailureCuts_directHealthyOwner generated objectsKnown
      (selectObjectFailureCuts_informative work [] _) objectUnique cuts
      (State.startup_runNormalized_atomicStreamActions_ordered startup valid)
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
  obtain ⟨received, input, later, sourceSplit, action, actualCut, ledger, _⟩ :=
    startup_atomicStream_sourcePrefix startup valid started selected rfl
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
          have health := generated.startup_activeObjectStreamHealthy_atSourceCut startup matched
            valid started
            located action actualCut failedPayloads
            (fun occurrence owners producer path result descriptor member => ?_)
            earlierSafe contributors
          · exact task_uncancelled_of_successfulProducerSafety known List.mem_cons_self health.2
              failedPayloads succeeded (by intro parent same; cases same; exact health.1)
          · have full := failedBefore_mono included (w.events.take cut).length member
            have atCut := failedBefore_subset w.failures (List.length_take_le _ _) full
            have objectMember := (cuts.object_mem_iff partition descriptor).mp atCut
            exact startup.informativeObjectFailureCuts_source_subset work inputs cut objectMember

/-- Both occurrence kinds license the same mixed startup inventory at its original cuts. -/
theorem startup_informativeFailureWitness {work inputs w streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work) startup).runNormalized
              inputs).2.flatten.flatMap
            publicationAtoms)
          streams)
    (exactCuts
      : w.failures
        = mergeFailureCuts (startup.informativeObjectFailureCuts work inputs) streams)
    : FailureWitness work (initialRefs work) w.matching w.events w.failures := by
  apply failureWitness announced
  intro before cut occurrence after split
  cases occurrence with
  | executionGroup address =>
      exact startup_informativeObjectFailures_uncancelled generated startup matched valid started
        announced safe
        cuts exactCuts before cut address after split
  | item address ordinal =>
      exact startup_informativeStreamFailures_uncancelled generated startup matched valid started
        announced safe
        cuts exactCuts before cut address ordinal after split

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
