import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemProducerPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupPublicationOwnership
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationItemProducer

/-! Startup item-produced objects retain strict publication on the shared matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- One retained item interpretation is shared with object and failure evidence
-----------------------------------------------------------------------------------------

/-- An item-produced raw releasing group places that item before this exact object atom.
Witness: raw source-boundary registration and item-first handling supply the prefix label;
unchanged item rank and the common ledger interpretation turn it into `Published`.
-/
theorem Witness.startup_groupPublication_groupItemProducerPublished
    {work inputs w index owner payload node dependencies source ordinal}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (origin
      : GroupPublicationOrigin
          {
            active :=
              ((State.initialize (Work.fromExecution work) startup)).initialGroups
              ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
          }
          (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
          index owner payload)
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (sameRef : node.ref = origin.group.ref)
    : Published w.matching (w.events.take index) (.item source ordinal) := by
  obtain ⟨_, _, _, _, interpret⟩ := ledger
  have atRaw : (((State.initialize (Work.fromExecution work)
    startup)).rawBatches
            inputs).2[origin.before.length]?
      = some (.groupValues origin.group origin.values) := by
    have same := congrArg (fun raw : List WorkQueueEvent => raw[origin.before.length]?)
      origin.rawEq
    simpa using same
  have delivered := generated.startup_rawBatches_groupValues_itemProducer_prefix startup matched
    valid started atRaw known sameRef
  have beforeEq : (((State.initialize (Work.fromExecution work)
    startup)).rawBatches
            inputs).2.take
      origin.before.length = origin.before := by
    have same := congrArg (List.take origin.before.length) origin.rawEq
    simpa using same
  rw [beforeEq] at delivered
  have rank := origin.itemRank
  have carrier := (Witness.startup_rawBatches_nonterminal startup history origin.carrier
    (by intro impossible; cases impossible)).1
  have within := (List.getElem?_eq_some_iff.mp carrier).1
  have earlier := origin.before_carrier
  rw [Witness.startup_rawBatches_prefix startup history index (by omega)] at rank
  apply interpret index
  rwa [rank]

/-- Every item-produced object publishes strictly after its producer under the same matching.
Witness: exact object provenance identifies the producer of its available raw releasing
owner. The raw group's item-origin theorem then proves the required strict publication;
no extra source order or independently supplied producer-publication premise is assumed.
-/
theorem StartupGroupPublicationReleases.itemProducerPublished
    {work inputs w index owner payload source ordinal} {startup : InitialStartup}
    (releases : StartupGroupPublicationReleases work startup inputs w)
    (generated : ExecutedWork work) (matchedStartup : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupValues owner payload))
    (produced : TaskHasProducer work (w.matching index) (some (.item source ordinal)))
    : Published w.matching (w.events.take index) (.item source ordinal) := by
  obtain ⟨origin, ⟨producer, known⟩, available⟩ :=
    releases.matched_available valid started history ledger selected
  obtain ⟨owners, taskPayload, descriptor⟩ := produced
  have sameProducer := (known.unique descriptor).2.1
  rw [sameProducer] at known
  cases matched : w.matching index with
  | item address itemIndex =>
      rw [matched] at known
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
      cases impossible
  | executionGroup address =>
      rw [matched] at known
      obtain ⟨node, dependencies, groupKnown, sameRef⟩ :=
        TaskAt.executionGroup_owner known available.1.2.1
      exact Witness.startup_groupPublication_groupItemProducerPublished generated startup
        matchedStartup valid started
        history ledger origin groupKnown sameRef

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
