import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFailureCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamOpenness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationAdmission

/-! Actual startup stream actions retain full health, closure admission and wire ownership. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A selected actual startup atom and its strict prefix keep their exact full-run positions. -/
theorem Witness.startup_event {work inputs index event} {w : Witness}
    (startup : InitialStartup)
    (history
      : w.events
        = (State.initialize (Work.fromExecution work) startup).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event)
    : let initial := State.initialize (Work.fromExecution work) startup
      let atoms := (initial.runNormalized inputs).2.flatten.flatMap publicationAtoms
      atoms[index]? = some event ∧ atoms.take index = w.events.take index := by
  let initial := State.initialize (Work.fromExecution work) startup
  have running := State.initializeWithStartup_terminated (Work.fromExecution work) startup
  have within := (List.getElem?_eq_some_iff.mp selected).1
  have bound : index < (initial.nonterminalAtoms inputs).length := history ▸ within
  constructor
  · rw [initial.runNormalized_terminalShape inputs running,
      List.getElem?_append_left bound, ← history]
    exact selected
  · rw [initial.nonterminalAtoms_startup_take inputs running (Nat.le_of_lt bound),
      ← history]

/-- A nonfailure stream action remains healthy under the shared startup failure inventory.
Actual release support handles object producers; source readiness and successful-item
safety handle root and item producers. No failure cut is moved to its notification.
-/
theorem startup_streamAction_healthy_of_successfulItems
    {work inputs w streams index event stream dependencies producer closing}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = (State.initialize (Work.fromExecution work) startup).nonterminalAtoms inputs)
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
    (known : NodeAt work stream .stream dependencies producer)
    (selected : w.events[index]? = some event)
    (action : streamAction event = some (stream.ref, closing))
    (nonfailure : ∀ node errors, event ≠ .streamFailure node errors)
    : ¬NodeFailed work w.matching (w.events.take index) w.failures stream.ref := by
  let objects := startup.informativeObjectFailureCuts work inputs
  have partition : w.failures.Perm (streams ++ objects) :=
    exactCuts ▸ mergeFailureCuts_partition objects streams
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
  have failedPayloads : ∀ cut occurrence,
      (cut, occurrence) ∈ w.failures
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true :=
    fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨owners, producer, path, errors, descriptor⟩ :=
      startup.objectReportingCuts_objectOrigin matched generated valid entry
        ((selectObjectFailureCuts_sublist work [] _).subset member)
    exact ⟨owners, producer, path, errors, descriptor⟩
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have contributors : ∀ occurrence owners,
      TaskHasOwners work occurrence owners → stream.ref ∈ owners
      → occurrence ∉ failedBefore w.failures (w.events.take index).length := by
    intro occurrence owners descriptor owner
    rw [length]
    exact cuts.no_failure_at_action_mixed partition objectKnown generated
      (State.startup_runNormalized_atomicStreamActions_ordered startup valid)
      known atFull action nonfailure descriptor owner
  obtain ⟨received, input, later, sourceSplit, sameAction, _, _, _⟩ :=
    startup_atomicStream_sourcePrefix startup valid started atFull action
  have sourcePrefix : (received ++ [input]).IsPrefix inputs.flatten :=
    ⟨later, by simp [sourceSplit, List.append_assoc]⟩
  have prior : received.IsPrefix inputs.flatten := ⟨input :: later, sourceSplit.symm⟩
  have localLaws := valid.atPrefix sourcePrefix
  have producerSucceeded := GraphEvent.Ready.streamProducer_succeeded
    localLaws.2.2 generated sameAction known
  have succeeded : ∀ source, producer = some source → TaskSucceeds work source :=
    fun source same => (valid.prefix prior).successes_succeed (producerSucceeded source same)
  have earlierSafe := safe.prefix prior index (List.Subset.refl w.failures)
  cases producer with
  | none =>
      have empty : dependencies = [] := by
        obtain ⟨_, _, atStream⟩ := known
        exact Correctness.located_producer_context atStream
      exact generated.streamHealthy_of_producerSafety failedPayloads known
        succeeded (by intro source impossible; cases impossible) contributors (.inl empty)
  | some parent =>
      cases parent with
      | item address ordinal =>
          have empty : dependencies = [] := by
            obtain ⟨_, _, atStream⟩ := known
            exact Correctness.located_producer_context atStream
          have parentSafe := earlierSafe address ordinal (producerSucceeded _ rfl)
          exact generated.streamHealthy_of_producerSafety failedPayloads known succeeded
            (by intro parent same; cases same; exact parentSafe) contributors (.inl empty)
      | executionGroup address =>
          obtain ⟨before, input, after, split, _, _, healthy⟩ :=
            generated.startup_atomicObjectStreamHealthy_of_earlierItems startup matched valid
              started cuts partition
              known atFull action nonfailure
          rw [beforeEq] at healthy
          have beforePrefix : before.IsPrefix inputs.flatten :=
            ⟨input :: after, split.symm⟩
          exact (healthy (safe.prefix beforePrefix index (List.Subset.refl w.failures))).2

/-- Actual startup stream successes satisfy their full local admission rule. -/
theorem startup_streamSuccessAdmission_of_successfulItems {work inputs w streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = (State.initialize (Work.fromExecution work) startup).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (accounted : StreamSuccessesAccounted work w)
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
    : StreamSuccessAdmission work w := by
  intro index stream selected
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
  have source := State.runNormalized_startup_streamCompletion_source
    (State.initialize (Work.fromExecution work) startup) inputs
    (List.mem_of_getElem? atFull) rfl
  obtain ⟨⟨dependencies, producer, address, entries, located⟩, _⟩ :=
    valid.streamSuccess_itemInventory generated source
  have known : NodeAt work stream .stream dependencies producer := .stream located
  have opened := generated.startup_runNormalized_streamOpenAt startup valid atFull
    List.mem_cons_self
  dsimp only at opened
  simp only [State.initializeWithStartup_initialGroups,
    State.initializeWithStartup_initialStreams] at opened
  rw [beforeEq] at opened
  have healthy := startup_streamAction_healthy_of_successfulItems generated startup matched valid
    started history
    announced safe cuts exactCuts known selected rfl (by intros; intro impossible; cases impossible)
  simp only [EventAllowed]
  rw [nodeFailed_filter (Nat.le_refl _)]
  exact ⟨
    ⟨dependencies, producer, known⟩,
    opened,
    healthy,
    accounted index stream selected _
  ⟩

/-- Startup stream values use their unique healthy open owner on the shared witness. -/
theorem startup_streamPublicationReady_of_certificates {work inputs w streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (coherent : NodeRefCoherent work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = (State.initialize (Work.fromExecution work) startup).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (ready : StreamValuesReady work w)
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
    : StreamPublicationReady work w := by
  intro index stream values groups children selected
  obtain ⟨value, producer, singleton, task, canPublish⟩ :=
    ready index stream values groups children selected
  obtain ⟨_, dependencies, known⟩ := itemTask_owner_nodeAt task
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
  have opened := generated.startup_runNormalized_streamOpenAt startup valid atFull
    List.mem_cons_self
  dsimp only at opened
  simp only [State.initializeWithStartup_initialGroups,
    State.initializeWithStartup_initialStreams] at opened
  rw [beforeEq] at opened
  have healthy := startup_streamAction_healthy_of_successfulItems generated startup matched valid
    started history
    announced safe cuts exactCuts known selected rfl
      (by intros; intro impossible; cases impossible)
  have active : OpenOwner work (initialRefs work) (w.events.take index) [stream.ref]
      stream := ⟨⟨.stream, dependencies, producer, known⟩, List.mem_cons_self, opened⟩
  refine ⟨value, producer, singleton, task, canPublish,
    active, ⟨stream, active, healthy⟩, ?_⟩
  intro other available
  obtain ⟨⟨kind, parents, source, otherKnown⟩, member, _⟩ := available
  have same := coherent other kind parents source stream .stream dependencies producer
    otherKnown known (List.mem_singleton.mp member)
  rw [same]
  exact Nat.le_refl _

/-- Actual failed stream closure has exact source metadata, an open ref, a licensed
historical failure and its exact single-cause diagnostic count on the shared witness.
-/
theorem startup_streamFailure_allowed {work inputs w index stream errors}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (history
      : w.events
        = (State.initialize (Work.fromExecution work) startup).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.streamFailure stream errors))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.streamFailure stream errors) w.reported := by
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
  have source := State.runNormalized_startup_streamCompletion_source
    (State.initialize (Work.fromExecution work) startup) inputs
    (List.mem_of_getElem? atFull) rfl
  obtain ⟨address, ordinal, producer, task, _, _⟩ :=
    valid.streamFailure_itemInventory generated source
  obtain ⟨dependencies, known⟩ := (itemTask_owner_nodeAt task).2
  have opened := generated.startup_runNormalized_streamOpenAt startup valid atFull
    List.mem_cons_self
  dsimp only at opened
  simp only [State.initializeWithStartup_initialGroups,
    State.initializeWithStartup_initialStreams] at opened
  rw [beforeEq] at opened
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have counts := announced.1.2.2.2.2 index stream errors selected
  have failed : NodeFailed work w.matching (w.events.take index) w.failures stream.ref :=
    nodeFailureCause_nodeFailed (length.symm ▸ counts)
  simp only [EventAllowed]
  rw [nodeFailed_filter (Nat.le_refl _), failedBefore_filter _ (Nat.le_refl _), length]
  exact ⟨⟨dependencies, producer, known⟩, opened, failed, counts⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
