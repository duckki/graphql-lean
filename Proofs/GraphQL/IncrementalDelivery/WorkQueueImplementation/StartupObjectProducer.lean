import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationProducerOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupAncestorProducerCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationItemProducer

/-! General object producer readiness on the unchanged common conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every object producer precedes its child object atom in actual normalized output.
Witness: generated defer continuity gives reused or ancestor support. Reused support uses
registration order within a shared block. Ancestor support now covers both prior activation
and activation inside either successful handler; exact raw offsets transport its strict
prefix to the same normalized matching and ledger. No handler-shape premise remains.
-/
theorem Witness.startup_groupPublication_objectProducerPublished
    {work inputs w index owner payload source} (generated : ExecutedWork work)
    (startup : InitialStartup) (matchedStartup : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupValues owner payload))
    (origin
      : GroupPublicationOrigin
          {
            active :=
              ((State.initialize (Work.fromExecution work) startup)).initialGroups
              ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
          }
          (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
          index owner payload)
    (rawKnown
      : ∃ dependencies producer, NodeAt work origin.group .group dependencies producer)
    (contributes
      : origin.group.ref ∈ origin.value.deliveryGroups.map Execution.DeliveryNode.ref)
    (produced : TaskHasProducer work (w.matching index) (some (.executionGroup source)))
    : Published w.matching (w.events.take index) (.executionGroup source) := by
  obtain ⟨producer, known⟩ := Witness.startup_groupPublication_taskAt startup started history
    ledger selected origin
  obtain ⟨owners, taskPayload, descriptor⟩ := produced
  have sameProducer := (known.unique descriptor).2.1
  rw [sameProducer] at known
  cases matched : w.matching index with
  | item address ordinal =>
      rw [matched] at known
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
      cases impossible
  | executionGroup address =>
      rw [matched] at known
      obtain ⟨node, dependencies, childKnown, sameRef⟩ :=
        TaskAt.executionGroup_owner known contributes
      obtain ⟨rawDependencies, rawProducer, rawKnown⟩ := rawKnown
      have sameNode := generated.nodeRefCoherent _ _ _ _ _ _ _ _ childKnown rawKnown sameRef
      rw [sameNode] at childKnown
      obtain ⟨parentOwners, ancestor, parentPayload, ref, parentKnown, parentContributes,
        support⟩ := generated.group_objectProducer_support childKnown
      rcases support with reused | dependency
      · apply Witness.startup_groupPublication_reusedProducerPublished generated startup
          matchedStartup valid started history
          ledger selected origin ⟨owners, taskPayload, descriptor⟩ parentKnown
        exact reused ▸ parentContributes
      · obtain ⟨published, batched, _, interpret, _⟩ := ledger
        have atRaw : (((State.initialize (Work.fromExecution work)
          startup)).rawBatches
            inputs).2[origin.before.length]?
            = some (.groupValues origin.group origin.values) := by
          have same := congrArg (fun raw : List WorkQueueEvent => raw[origin.before.length]?)
            origin.rawEq
          simpa using same
        obtain ⟨value, delivered⟩ := generated.startup_rawBatches_ancestorProducer_beforeValue
          startup matchedStartup valid started batched atRaw known contributes
          (groupRecordAt_of_nodeAt childKnown)
          dependency parentKnown parentContributes
        have beforeEq : (((State.initialize (Work.fromExecution work)
          startup)).rawBatches
            inputs).2.take
              origin.before.length
            = origin.before := by
          have same := congrArg (List.take origin.before.length) origin.rawEq
          simpa using same
        rw [beforeEq] at delivered
        have rank := origin.objectRank
        rw [(Witness.startup_rawBatches_canonical startup history selected).2] at rank
        apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
        rw [← List.map_take]
        apply List.mem_map.mpr
        refine ⟨(_, value), ?_, rfl⟩
        exact List.take_subset_take_left _ (by omega) delivered

/-- Every actual object value has its structural producer in the strict output prefix.
Witness: the actual release origin supplies raw group provenance and contributor identity.
Object producers use the complete handler argument; item producers use item-first output
order. Both cases retain the same publication matching and exact replay ledger.
-/
theorem StartupGroupPublicationReleases.producerPublished
    {work inputs w index owner payload parent} {startup : InitialStartup}
    (releases : StartupGroupPublicationReleases work startup inputs w)
    (generated : ExecutedWork work) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupValues owner payload))
    (produced : TaskHasProducer work (w.matching index) (some parent))
    : Published w.matching (w.events.take index) parent := by
  cases parent with
  | item source ordinal =>
      exact releases.itemProducerPublished generated matched valid started history ledger
        selected produced
  | executionGroup source =>
      obtain ⟨origin, rawKnown, _, _⟩ := releases index owner payload selected
      have contributes := State.startup_rawBatches_publicationContributors startup valid
        origin.group origin.values origin.members.1 origin.value origin.members.2
      exact Witness.startup_groupPublication_objectProducerPublished generated startup matched
        valid started history
        ledger selected origin rawKnown contributes produced

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
