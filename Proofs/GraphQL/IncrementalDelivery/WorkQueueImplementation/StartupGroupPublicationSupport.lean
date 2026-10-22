import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationSupport

/-! Actual startup raw release groups support remapped object publication. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every actual startup object atom retains its exact raw release pair under the same
publisher, including the real positions of initial diagnostic controls.
-/
theorem Witness.startup_groupPublication_origin {work inputs} {w : Witness}
    {index owner payload} (startup : InitialStartup)
    (_started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupValues owner payload))
    : let queue := (State.initialize (Work.fromExecution work) startup)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      Nonempty
        (GroupPublicationOrigin publisher
          (queue.rawBatches inputs).2
          index owner payload) := by
  have atRaw := (Witness.startup_rawBatches_canonical startup history selected).1
  let initial := State.initialize (Work.fromExecution work) startup
  exact (initial.rawBatches_publicationPairs inputs).normalized_origin _ atRaw

/-- The actual raw release group is known, open, and historically healthy at its value.
The selected wire owner may be different, and may already be failed. Contributor
membership and longest-open owner selection remain separate obligations.
Witness: its unchanged successful carrier supplies provenance and durable health; the
intervening object-only segment has exactly the same notice state.
-/
theorem Witness.startup_groupPublication_releaseReady {work inputs w index owner payload}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (healthy : GroupSuccessesHealthy work w)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              ((State.initialize (Work.fromExecution work) startup)).initialGroups
              ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
          }
          (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
          index owner payload)
    : (∃ dependencies producer, NodeAt work origin.group .group dependencies producer)
      ∧ Open (initialRefs work) (w.events.take index) origin.group.ref
      ∧ ¬NodeFailed work w.matching (w.events.take index) w.failures
          origin.group.ref := by
  obtain ⟨carrier, carrierPrefix⟩ :=
    Witness.startup_rawBatches_nonterminal startup history origin.carrier
    (by intro impossible; cases impossible)
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history carrier
  have known := generated.startup_runNormalized_atomicGroupClosuresLocated startup valid _
    (List.mem_of_getElem? atFull)
  have opened := generated.startup_runNormalized_groupClosureOpenAt startup valid started atFull
    List.mem_cons_self
  dsimp only at opened
  rw [beforeEq] at opened
  have noticeState := origin.noticeState
  dsimp only at noticeState
  have within := (List.getElem?_eq_some_iff.mp carrier).1
  have earlier := origin.before_carrier
  rw [Witness.startup_rawBatches_prefix startup history index (by omega), carrierPrefix]
    at noticeState
  refine ⟨known, ?_, healthy.atPrefix carrier index⟩
  simpa only [Open, announcedRefs, initialRefs, initialQueue,
    State.initializeWithStartup_initialGroups, State.initializeWithStartup_initialStreams,
    noticeState.1, noticeState.2]
    using opened

/-- Every object atom retains its actual release origin and that group's known, open,
healthy status. This is weaker than `PublicationAdmission`: it does not yet connect the
raw group's task memberships to the shared matching or validate the remapped owner.
-/
def StartupGroupPublicationReleases (work : Execution.Work) (startup : InitialStartup)
    (inputs : List (List GraphEvent)) (w : Witness)
    : Prop :=
  ∀ index owner payload,
    w.events[index]? = some (.groupValues owner payload)
    → ∃ origin
          : GroupPublicationOrigin
              {
                active :=
                  ((State.initialize (Work.fromExecution work) startup)).initialGroups
                  ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
              }
              (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
              index owner payload,
        (∃ dependencies producer, NodeAt work origin.group .group dependencies producer)
        ∧ Open (initialRefs work) (w.events.take index) origin.group.ref
        ∧ ¬NodeFailed work w.matching (w.events.take index) w.failures origin.group.ref

/-- All actual object publications have healthy raw release groups on the shared witness.
Witness: recover each raw pair, then reuse successful-carrier health and unchanged notice
state. The input laws are unchanged and no publication-admission premise is used.
-/
theorem startup_groupPublicationReleases_of_groupHealth {work inputs w}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (healthy : GroupSuccessesHealthy work w)
    : StartupGroupPublicationReleases work startup inputs w := by
  intro index owner payload selected
  obtain ⟨origin⟩ := Witness.startup_groupPublication_origin startup started history selected
  exact ⟨origin, Witness.startup_groupPublication_releaseReady generated startup valid started
    history
    healthy origin⟩

/-- Every retained raw release group is an available contributing owner for its full value.
Witness: actual raw membership supplies the owner ref; the release certificate supplies
provenance, openness, and health on the same history, matching, and failure cuts.
Connecting that value to the selected matching occurrence remains a separate ledger step.
-/
theorem StartupGroupPublicationReleases.available {work inputs w}
    {startup : InitialStartup}
    (releases : StartupGroupPublicationReleases work startup inputs w)
    (valid : ValidGraphEvents work inputs.flatten) {index owner payload}
    (selected : w.events[index]? = some (.groupValues owner payload))
    : ∃ origin
          : GroupPublicationOrigin
              {
                active :=
                  ((State.initialize (Work.fromExecution work) startup)).initialGroups
                  ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
              }
              (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
              index owner payload,
        HealthyOpenOwner work (initialRefs work) w.matching (w.events.take index)
          w.failures (origin.value.deliveryGroups.map Execution.DeliveryNode.ref)
          origin.group := by
  obtain ⟨origin, ⟨dependencies, producer, known⟩, opened, healthy⟩ :=
    releases index owner payload selected
  have member := State.startup_rawBatches_publicationContributors startup valid
    origin.group origin.values origin.members.1 origin.value origin.members.2
  exact ⟨origin, ⟨⟨.group, dependencies, producer, known⟩, member, opened⟩, healthy⟩

/-- The raw release origin retains every contributor's structural descriptor.
Witness: recover its actual successful source input with the full contributor-bearing
value, then apply source matching. Equal response data does not identify a task here.
-/
theorem Witness.startup_groupPublication_contributorsLocated {work}
    (startup : InitialStartup) {inputs : List (List GraphEvent)} {index owner payload}
    (valid : ValidGraphEvents work inputs.flatten)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              ((State.initialize (Work.fromExecution work) startup)).initialGroups
              ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
          }
          (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
          index owner payload)
    : ∀ contributor ∈ origin.value.deliveryGroups,
        ∃ dependencies producer,
          NodeAt work contributor .group dependencies producer := by
  obtain ⟨occurrence, result, _, same, source⟩ :=
    State.startup_rawBatches_valueSource startup valid origin.members.1 origin.members.2
  intro contributor member
  exact source.success_contributorsLocated contributor (same.symm ▸ member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
