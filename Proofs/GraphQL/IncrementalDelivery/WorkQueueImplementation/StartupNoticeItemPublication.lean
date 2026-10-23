import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeCarrierCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemProducerPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeItemPublication

/-! Startup group notices retain the producer item on the same inclusive publication cut. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Either notice carrier supplies the same inclusive raw item prefix
-----------------------------------------------------------------------------------------

/-- A canonical group notice retains its raw carrier and inclusive item-prefix count.
Witness: group carriers preserve their strict rank and carry no items; item notices occur
only on the final atom of their raw batch. Both retain the same noticed ref and index.
-/
theorem Witness.startup_groupNotice_itemRawPrefix {work inputs} {w : Witness}
    {index event ref} (startup : InitialStartup)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event) (noticed : ref ∈ groupNoticeRefs event)
    : ∃ position output,
        (((State.initialize (Work.fromExecution work) startup)).rawBatches
            inputs).2[position]?
          = some output
        ∧ ref ∈ rawGroupNoticeRefs output
        ∧ ((w.events.take (index + 1)).flatMap normalizedItemValues).length
          = (((((State.initialize (Work.fromExecution work) startup)).rawBatches
                inputs).2.take
                (position + 1)).flatMap
              WorkQueueEvent.itemValues).length := by
  cases event with
  | groupSuccess group groups streams =>
      obtain ⟨atFull, prefixEq⟩ := Witness.startup_rawBatches_canonical startup history selected
      obtain ⟨sourceIndex, atSource, sourceCount⟩ :=
        publicationAtoms_groupSuccess_itemPrefix _ atFull
      obtain ⟨position, atRaw, rawCount⟩ :=
        IncrementalPublisher.normalizeBatch_groupSuccess_itemPrefix _ _ atSource
      refine ⟨position, _, atRaw, noticed, ?_⟩
      simp only [List.take_add_one, selected, atRaw, Option.toList_some,
        List.flatMap_append, List.flatMap_singleton, normalizedItemValues,
        WorkQueueEvent.itemValues, List.append_nil]
      rw [← prefixEq]
      exact sourceCount.trans rawCount
  | streamValues owner values groups streams =>
      obtain ⟨child, member, same⟩ := List.mem_map.mp noticed
      obtain ⟨position, rawValues, atRaw, _, itemCount⟩ :=
        w.startup_itemNotice_rawPrefix startup started history selected
          (List.mem_append_left streams member)
      refine ⟨position, _, atRaw, ?_, itemCount⟩
      exact List.mem_map.mpr ⟨child, member, same⟩
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases noticed

/-- Every item-produced group notice has its producer published by the carrier's end.
Witness: its actual raw handler registers the group only after the producer input. The
same inclusive item rank survives normalization and atomic splitting; the shared ledger
interprets that source occurrence with the original matching, not a separately chosen one.
-/
theorem Witness.startup_groupNotice_itemProducerPublished
    {work inputs} {w : Witness} {index event node dependencies source ordinal}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some event)
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (noticed : node.ref ∈ groupNoticeRefs event)
    : Published w.matching (w.events.take (index + 1)) (.item source ordinal) := by
  obtain ⟨_, _, _, _, interpret⟩ := ledger
  obtain ⟨position, output, atRaw, rawNotice, itemCount⟩ :=
    w.startup_groupNotice_itemRawPrefix startup started history selected noticed
  have delivered := generated.startup_rawBatches_groupNotice_itemProducer_prefix startup matched
    valid started
    atRaw known rawNotice
  apply interpret (index + 1)
  rwa [itemCount]

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
