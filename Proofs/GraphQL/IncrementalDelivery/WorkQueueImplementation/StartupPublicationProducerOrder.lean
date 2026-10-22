import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupPublicationOwnership
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayBlockOrder

/-! Startup shared-owner producers precede their children on the same publication ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Source-valid startup replay retains strict producer order on each exact raw block.
The initial cache changes neither permanent task order nor the shared closure ledger.
-/
theorem startup_batch_blockProducerOrder {work batches published index group values}
    (startup : InitialStartup)
    (covered
      : ((State.initialize (Work.fromExecution work) startup)).BatchClosuresCovered
          batches published)
    (started : inputsStarted work batches startup = true)
    (valid : ValidGraphEvents work batches.flatten)
    (selected
      : (((State.initialize (Work.fromExecution work) startup)).rawBatches
          batches).2[index]?
        = some (.groupValues group values))
    : ProducerOrder work
        ((published.drop
            (((((State.initialize (Work.fromExecution work) startup)).rawBatches
                batches).2.take
                index).flatMap
              WorkQueueEvent.objectValues).length).take
            values.length
          |>.map Prod.fst) := by
  have initial := State.initializeWithStartup_producerOrder work startup
  have ordered := ((State.initialize (Work.fromExecution work)
    startup)).rawBatches_producerOrder (before := []) initial.1 initial.2 batches valid
      (by rwa [← inputsStartedWithStartup_eq_batchesStarted])
  exact ordered.2.sublist (covered.blocks_rawBatches.atEvent selected)

-----------------------------------------------------------------------------------------
-- Reused owners cover the producer in this block or in an earlier publication
-----------------------------------------------------------------------------------------

/-- An object producer sharing the releasing group publishes strictly before its child.
Witness: structural carrier coverage puts the producer before the block's closing event.
It is either in an earlier block or in this block; retained registration order makes the
second case strictly earlier than the child. All steps use the existing exact ledger,
matching, and failure cuts, without a supplied storage or producer-publication premise.
-/
theorem Witness.startup_groupPublication_reusedProducerPublished
    {work inputs w index owner payload source parentOwners ancestor parentPayload}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
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
    (produced : TaskHasProducer work (w.matching index) (some (.executionGroup source)))
    (parent : TaskAt work (.executionGroup source) parentOwners ancestor parentPayload)
    (contributes : origin.group.ref ∈ parentOwners)
    : Published w.matching (w.events.take index) (.executionGroup source) := by
  obtain ⟨published, batched, exactLedger, interpret, _⟩ := ledger
  have atCarrier : (((State.initialize (Work.fromExecution work)
    startup)).rawBatches
            inputs).2[origin.before.length + 1]?
      = some (.groupSuccess origin.group origin.groups origin.streams) := by
    have output := congrArg (fun raw : List WorkQueueEvent =>
      raw[origin.before.length + 1]?) origin.rawEq
    simpa using output
  obtain ⟨parentValue, covered⟩ := generated.startup_rawBatches_groupContributor_covered
    startup matched valid started batched atCarrier parent contributes
  have countAtCarrier :
      ((((((State.initialize (Work.fromExecution work) startup)).rawBatches
            inputs).2.take
          (origin.before.length + 1)).flatMap WorkQueueEvent.objectValues).length)
        = (origin.before.flatMap WorkQueueEvent.objectValues).length + origin.values.length := by
    have output := congrArg (fun raw : List WorkQueueEvent =>
      ((raw.take (origin.before.length + 1)).flatMap WorkQueueEvent.objectValues).length)
      origin.rawEq
    simpa [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      WorkQueueEvent.objectValues] using output
  rw [countAtCarrier, List.take_add] at covered
  have rank := origin.objectRank
  rw [(Witness.startup_rawBatches_canonical startup history selected).2] at rank
  have atObject := exactLedger.atObject index owner payload selected
  rw [rank, List.getElem?_map] at atObject
  have within := (List.getElem?_eq_some_iff.mp origin.found).1
  have parentBefore : ∃ value, (Occurrence.executionGroup source, value)
        ∈ published.take ((w.events.take index).flatMap normalizedObjectValues).length := by
    rw [rank, List.take_add]
    rcases List.mem_append.mp covered with earlier | sameBlock
    · exact ⟨parentValue, List.mem_append_left _ earlier⟩
    · cases found
            : published[(origin.before.flatMap WorkQueueEvent.objectValues).length
                        + origin.offset]? with
      | none => simp only [found, Option.map_none, reduceCtorEq] at atObject
      | some entry =>
          have same : entry.1 = w.matching index := by
            simpa only [found, Option.map_some, Option.some.injEq] using atObject
          have atRaw : (((State.initialize (Work.fromExecution work)
            startup)).rawBatches
            inputs).2[origin.before.length]?
              = some (.groupValues origin.group origin.values) := by
            have output := congrArg (fun raw : List WorkQueueEvent =>
              raw[origin.before.length]?) origin.rawEq
            simpa using output
          have ordered := startup_batch_blockProducerOrder startup batched started valid atRaw
          have beforeEq : (((State.initialize (Work.fromExecution work)
            startup)).rawBatches
            inputs).2.take
              origin.before.length = origin.before := by
            have output := congrArg (List.take origin.before.length) origin.rawEq
            simpa using output
          rw [beforeEq] at ordered
          have childAt : ((published.drop
              (origin.before.flatMap WorkQueueEvent.objectValues).length).take
                origin.values.length)[origin.offset]? = some entry := by
            rw [List.getElem?_take_of_lt within, List.getElem?_drop]
            exact found
          obtain ⟨value, earlier⟩ := ordered.publication_before childAt (same.symm ▸ produced)
            (List.mem_map.mpr ⟨_, sameBlock, rfl⟩)
          rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt within)] at earlier
          exact ⟨value, List.mem_append_right _ earlier⟩
  obtain ⟨value, earlier⟩ := parentBefore
  apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  rw [← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), earlier, rfl⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
