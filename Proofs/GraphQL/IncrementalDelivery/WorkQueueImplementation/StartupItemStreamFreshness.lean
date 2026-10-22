import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalItemStreamFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupNoticeMetadata

/-! Startup item carriers announce fresh, internally unique stream and group refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- An announced structural stream ref came from an initial or carried stream notice.
Witness: generated node roles exclude initial supported group refs and actual group
notices. This does not assume either notice freshness or output admission.
-/
theorem startup_streamNode_announced_stream
    {work inputs index child dependencies producer} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (known : NodeAt work child .stream dependencies producer)
    (announced : child.ref ∈ announcedRefs (initialRefs work) (w.events.take index))
    : child.ref
      ∈ (initialQueue work).initialStreams.map Execution.DeliveryNode.ref
        ++ (w.events.take index).flatMap streamNoticeRefs := by
  rcases List.mem_append.mp announced with initial | pending
  · rw [initialRefs, List.map_append] at initial
    rcases List.mem_append.mp initial with group | stream
    · have active : child.ref ∈ (initialQueue work).rootGroups := by
        rwa [createWorkQueue_rootGroups]
      obtain ⟨parents, group, birth, descriptor, same⟩ :=
        (createWorkQueue_fromSpec_groupRefSupport work).roots child.ref active
      exact False.elim (generated.groupStreamRefsDisjoint descriptor known same)
    · exact List.mem_append_left _ stream
  · obtain ⟨event, prior, notice⟩ := List.mem_flatMap.mp pending
    obtain ⟨position, selected⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take prior)
    have groupsKnown := State.startup_runNormalized_atomicGroupNoticesLocated generated startup
      valid event
      (List.mem_of_getElem? (Witness.startup_event startup history selected).1)
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨event, prior, ?_⟩
    cases event <;> simp only [eventPending] at notice
    case groupSuccess group groups streams | streamValues group values groups streams =>
      rw [List.map_append] at notice
      rcases List.mem_append.mp notice with groupNotice | streamNotice
      · obtain ⟨group, member, same⟩ := List.mem_map.mp groupNotice
        obtain ⟨parents, birth, descriptor⟩ := groupsKnown group member
        exact False.elim (generated.groupStreamRefsDisjoint descriptor known same)
      · exact streamNotice
    all_goals cases notice

/-- A canonical item notice retains its exact raw strict stream-notice prefix.
Witness: started replay supplies the actual publisher history; final-item atomization
and normalization preserve one common indexed carrier and all preceding stream notices.
-/
theorem Witness.startup_itemNotice_rawStreamPrefix {work inputs} {w : Witness}
    {index owner values groups streams child}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (_started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ position rawValues,
        (((State.initialize (Work.fromExecution work) startup)).rawBatches
            inputs).2[position]?
          = some (.streamValues owner rawValues groups streams)
        ∧ (w.events.take index).flatMap streamNoticeRefs
          = ((((State.initialize (Work.fromExecution work) startup)).rawBatches
                inputs).2.take
              position).flatMap
              rawStreamNoticeRefs := by
  obtain ⟨atAtoms, exactPrefix⟩ := Witness.startup_rawBatches_canonical startup history selected
  have rawShape := ((State.initialize (Work.fromExecution work)
    startup)).rawBatches_nonemptyValues
      inputs valid.nonemptyItems
  obtain ⟨sourceIndex, sourceValues, sourceAt, notices⟩ :=
    publicationAtoms_itemNotice_streamPrefix _
      (IncrementalPublisher.normalizeBatch_nonemptyValues _ _ rawShape).2 atAtoms noticed
  obtain ⟨position, rawValues, rawAt, rawNotices⟩ :=
    IncrementalPublisher.normalizeBatch_itemNotice_streamPrefix _ _ sourceAt
  rw [exactPrefix] at notices
  exact ⟨position, rawValues, rawAt, notices.trans rawNotices⟩

/-- An actual item-carried stream notice is fresh against every earlier announcement.
Witness: role separation discards group notices, and the exact raw prefix uses permanent
stream registration to exclude both initial notices and previously closed streams.
-/
theorem startup_itemStreamNotice_fresh
    {work inputs index owner values groups streams child} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ streams)
    : child.ref ∉ announcedRefs (initialRefs work) (w.events.take index) := by
  have known := State.startup_runNormalized_atomicStreamNoticesLocated startup valid _
    (List.mem_of_getElem? (Witness.startup_event startup history selected).1) child noticed
  obtain ⟨dependencies, producer, descriptor⟩ := known
  obtain ⟨position, rawValues, rawAt, notices⟩ := Witness.startup_itemNotice_rawStreamPrefix
    startup valid started history selected (List.mem_append_right groups noticed)
  intro announced
  have repeated := startup_streamNode_announced_stream generated startup valid history descriptor
    announced
  rw [notices] at repeated
  apply ((State.initialize (Work.fromExecution work)
            startup)).rawBatches_itemStreamNoticeFresh
    inputs rawAt noticed
  rcases List.mem_append.mp repeated with initial | prior
  · apply List.mem_append_left
    obtain ⟨node, member, same⟩ := List.mem_map.mp initial
    have registered := (State.maybeIntegrateWork_streams_registered ({} : State)
      (Work.fromExecution work)).2 member
    obtain ⟨stream, stored, equal⟩ := List.mem_map.mp registered
    have registry : (initialQueue work).streams
        = (({} : State).maybeIntegrateWork (Work.fromExecution work)).1.streams := by
      let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
      let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
      change (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 }).1.streams
        = integrated.1.streams
      rw [State.startNewWork_streams, State.pruneEmptyGroups_streams]
    rw [State.initializeWithStartup_streams, registry]
    exact List.mem_map.mpr ⟨stream, stored,
      (congrArg Execution.DeliveryNode.ref equal).trans same⟩
  · exact List.mem_append_right _ prior

-----------------------------------------------------------------------------------------
-- Both child lists on one item carrier have distinct refs
-----------------------------------------------------------------------------------------

/-- A canonical item carrier's stream-notice refs are internally unique.
Witness: recover its exact raw handler and reuse the concrete multi-item fresh inventory;
an empty notice list is immediate and requires no carrier-position inversion.
-/
theorem startup_itemStreamNoticeRefs_nodup {work inputs owner values groups streams}
    {index : Nat} {w : Witness} (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    : (streams.map Execution.DeliveryNode.ref).Nodup := by
  cases streams with
  | nil => simp
  | cons child rest =>
      obtain ⟨position, rawValues, rawAt, _⟩ := Witness.startup_itemNotice_rawStreamPrefix
        startup valid started history selected (List.mem_append_right groups List.mem_cons_self)
      obtain ⟨earlier, batch, later, fifo, event, tail, localIndex, _, _, emitted, _⟩ :=
        ((State.initialize (Work.fromExecution work)
          startup)).rawBatches_immediate_rawCut inputs rawAt
          (by intro group errors impossible; cases impossible)
          (by intro impossible; cases impossible)
      let available := GraphEvent.availableFailures batch
      let current := (((State.initialize (Work.fromExecution work)
        startup)).replayBatches earlier).replayGraphEvents fifo available
      obtain ⟨stream, items, rfl⟩ :=
        current.handleGraphEvent_streamValues_source event available emitted
      exact ((current.cacheTaskFailures available).streamItems_notices_fresh stream items
        available emitted).1

/-- The combined group/stream notice list on an item carrier has no repeated ref.
Witness: global group uniqueness gives its group sublist; fresh registration gives stream
uniqueness; generated group/stream roles exclude collisions between the two lists.
-/
theorem startup_itemNoticeRefs_nodup {work inputs owner values groups streams}
    {index : Nat} {w : Witness} (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    : ((groups ++ streams).map Execution.DeliveryNode.ref).Nodup := by
  have unique := (List.nodup_append.mp
    (startup_groupNoticeRefs_nodup generated startup matched valid started history)).2.1
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp (List.mem_of_getElem? selected)
  rw [split, List.flatMap_append, List.flatMap_cons] at unique
  have groupsUnique := (List.nodup_append.mp (List.nodup_append.mp unique).2.1).1
  have atFull := List.mem_of_getElem? (Witness.startup_event startup history selected).1
  have groupKnown := State.startup_runNormalized_atomicGroupNoticesLocated generated startup valid
    _ atFull
  have streamKnown := State.startup_runNormalized_atomicStreamNoticesLocated startup valid _ atFull
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨groupsUnique,
    startup_itemStreamNoticeRefs_nodup startup valid started history selected, ?_⟩
  intro first groupMember second streamMember same
  obtain ⟨group, included, groupRef⟩ := List.mem_map.mp groupMember
  obtain ⟨stream, noticed, streamRef⟩ := List.mem_map.mp streamMember
  obtain ⟨parents, birth, descriptor⟩ := groupKnown group included
  obtain ⟨enclosing, producer, known⟩ := streamKnown stream noticed
  exact generated.groupStreamRefsDisjoint descriptor known
    (groupRef.trans (same.trans streamRef.symm))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
