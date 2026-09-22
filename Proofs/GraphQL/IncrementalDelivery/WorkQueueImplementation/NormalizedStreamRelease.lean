import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseReplay

/-! Publisher normalization and complete replay preserve the same release inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Normalization preserves stream carriers and their preceding object-value counts
-----------------------------------------------------------------------------------------

/-- Normalize the head event before normalizing the tail with its updated publisher.
Witness: the actual fold accumulates output by concatenation and changes no earlier output.
-/
theorem IncrementalPublisher.normalizeBatch_cons (publisher : IncrementalPublisher)
    (event : WorkQueueEvent) (events : List WorkQueueEvent)
    : publisher.normalizeBatch (event :: events)
      = let head := publisher.handleWorkQueueEvent event
        let tail := head.1.normalizeBatch events
        (tail.1, head.2 ++ tail.2) := by
  let step (acc : IncrementalPublisher × List Execution.WorkQueueEvent) (event : WorkQueueEvent) :=
    let next := acc.1.handleWorkQueueEvent event
    (next.1, acc.2 ++ next.2)
  have accumulator (events : List WorkQueueEvent) (current : IncrementalPublisher)
      (before : List Execution.WorkQueueEvent)
      : events.foldl step (current, before)
        = ((current.normalizeBatch events).1,
            before ++ (current.normalizeBatch events).2) := by
    induction events generalizing current before with
    | nil => simp [IncrementalPublisher.normalizeBatch]
    | cons head rest ih =>
        simp only [List.foldl_cons, step]
        rw [ih]
        change _ = ((rest.foldl step _).1, before ++ (rest.foldl step _).2)
        rw [ih]
        simp only [List.append_assoc, List.nil_append]
  change events.foldl step _ = _
  simpa only [step, List.nil_append]
    using accumulator events (publisher.handleWorkQueueEvent event).1
      (publisher.handleWorkQueueEvent event).2

/-- A normalized group-success carrier is the unchanged singleton of that raw event.
Witness: object normalization emits only object events; every other constructor keeps its
own distinct tag. Thus no owner choice creates, removes, or moves a carrier within an event.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupSuccess
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    {index group groups streams}
    (atEvent
      : (publisher.handleWorkQueueEvent event).2[index]?
        = some (.groupSuccess group groups streams))
    : event = .groupSuccess group groups streams ∧ index = 0 := by
  have member := List.mem_of_getElem? atEvent
  cases event with
  | groupValues owner values =>
      obtain ⟨value, _, impossible⟩ := List.mem_map.mp member
      cases impossible
  | groupSuccess owner newGroups newStreams =>
      have same : owner = group ∧ newGroups = groups ∧ newStreams = streams := by
        simpa [IncrementalPublisher.handleWorkQueueEvent]
          using (List.mem_singleton.mp member).symm
      obtain ⟨rfl, rfl, rfl⟩ := same
      refine ⟨rfl, ?_⟩
      by_cases zero : index = 0
      · exact zero
      · simp [IncrementalPublisher.handleWorkQueueEvent, zero] at atEvent
  | groupFailure | streamValues | streamSuccess | streamFailure | workQueueTermination =>
      simp [IncrementalPublisher.handleWorkQueueEvent] at member

/-- Every normalized stream carrier retains its raw position's preceding object count.
Witness: induction through the stateful publisher fold. Singleton object expansion changes
event indices but preserves value counts; the carrier itself remains a singleton.
-/
theorem IncrementalPublisher.normalizeBatch_groupSuccess
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    {index group groups streams}
    (atEvent
      : (publisher.normalizeBatch events).2[index]?
        = some (.groupSuccess group groups streams))
    : ∃ rawIndex,
        events[rawIndex]? = some (.groupSuccess group groups streams)
        ∧ (((publisher.normalizeBatch events).2.take index).flatMap
            normalizedObjectValues).length
          = ((events.take rawIndex).flatMap WorkQueueEvent.objectValues).length := by
  induction events generalizing publisher index with
  | nil => simp [IncrementalPublisher.normalizeBatch] at atEvent
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons] at atEvent ⊢
      dsimp only at atEvent ⊢
      let head := publisher.handleWorkQueueEvent event
      let tail := head.1.normalizeBatch rest
      change (head.2 ++ tail.2)[index]? = _ at atEvent
      by_cases earlier : index < head.2.length
      · have atHead := (List.getElem?_append_left earlier).symm.trans atEvent
        obtain ⟨rfl, rfl⟩ := publisher.handleWorkQueueEvent_groupSuccess event atHead
        exact ⟨0, rfl, rfl⟩
      · have later : head.2.length ≤ index := by omega
        have atTail := (List.getElem?_append_right later).symm.trans atEvent
        obtain ⟨rawIndex, rawEvent, count⟩ := ih head.1 atTail
        refine ⟨rawIndex + 1, rawEvent, ?_⟩
        change (((head.2 ++ tail.2).take index).flatMap normalizedObjectValues).length = _
        rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
          List.length_append, count]
        have headCount := congrArg List.length
          (publisher.handleWorkQueueEvent_objectValues event)
        simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
        exact congrArg (· + _) headCount

-----------------------------------------------------------------------------------------
-- Reuse the exact raw inventory, without reconstructing identities from equal payloads
-----------------------------------------------------------------------------------------

/-- At each normalized group-success carrier, the stream producer labels an earlier object
publication in `published`. Exact payload preservation and freshness are separate facts.
-/
def NormalizedStreamReleasePublications (work : Execution.Work)
    (published : List ObjectPublication) (events : List Execution.WorkQueueEvent)
    : Prop :=
  ∀ index group groups streams,
    events[index]? = some (.groupSuccess group groups streams)
    → ∀ stream ∈ streams,
        ∀ dependencies producer,
          NodeAt work stream .stream dependencies producer
          → ∃ occurrence,
              producer = some occurrence
              ∧ occurrence
                ∈ (published.take
                    ((events.take index).flatMap normalizedObjectValues).length).map
                    Prod.fst

/-- Owner remapping preserves release support with the original occurrence labels.
Witness: each normalized carrier has the same raw carrier and preceding value count.
No equality of payloads is used to choose or identify its source occurrence.
-/
theorem StreamReleasePublications.normalizeBatch {work published events}
    (supported : StreamReleasePublications work published events)
    (publisher : IncrementalPublisher)
    : NormalizedStreamReleasePublications work published
        (publisher.normalizeBatch events).2 := by
  intro index group groups streams atEvent stream member dependencies producer known
  obtain ⟨rawIndex, rawEvent, count⟩ := publisher.normalizeBatch_groupSuccess events atEvent
  rw [count]
  exact supported rawIndex group groups streams rawEvent stream member dependencies producer known

/-- Empty normalized output has no carrier requiring earlier publication.
Witness: no index can select an event from an empty list. -/
theorem NormalizedStreamReleasePublications.nil (work : Execution.Work)
    : NormalizedStreamReleasePublications work [] [] := by
  intro index group groups streams impossible
  simp at impossible

/-- Concatenated normalized output retains release support in one concatenated inventory.
Witness: carrier indices split between the segments; exact earlier payload preservation supplies
the inventory offset, independently of owner remapping and equal-valued publications.
-/
theorem NormalizedStreamReleasePublications.append {work first second left right}
    (before : NormalizedStreamReleasePublications work first left)
    (after : NormalizedStreamReleasePublications work second right)
    (values
      : first.map (fun publication => publication.2)
        = left.flatMap normalizedObjectValues)
    : NormalizedStreamReleasePublications work (first ++ second) (left ++ right) := by
  have size : first.length = (left.flatMap normalizedObjectValues).length := by
    simpa only [List.length_map] using congrArg List.length values
  intro index group groups streams atEvent stream member dependencies producer known
  by_cases earlier : index < left.length
  · have atLeft := (List.getElem?_append_left earlier).symm.trans atEvent
    obtain ⟨occurrence, same, published⟩ :=
      before index group groups streams atLeft stream member dependencies producer known
    have count : ((left.take index).flatMap normalizedObjectValues).length ≤ first.length := by
      have split := congrArg (fun events : List Execution.WorkQueueEvent =>
        (events.flatMap normalizedObjectValues).length) (List.take_append_drop index left)
      simp only [List.flatMap_append, List.length_append] at split
      omega
    refine ⟨occurrence, same, ?_⟩
    rw [List.take_append_of_le_length (Nat.le_of_lt earlier),
      List.take_append_of_le_length count]
    exact published
  · have later : left.length ≤ index := by omega
    have atRight := (List.getElem?_append_right later).symm.trans atEvent
    obtain ⟨occurrence, same, published⟩ := after (index - left.length) group groups streams
      atRight stream member dependencies producer known
    refine ⟨occurrence, same, ?_⟩
    rw [List.take_append (l₁ := left), List.take_of_length_le later, List.flatMap_append,
      List.length_append, ← size, List.take_append (l₁ := first)]
    simp only [List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.map_append]
    exact List.mem_append_right _ published

-----------------------------------------------------------------------------------------
-- All actual normalized batches share the same fresh occurrence-labelled inventory
-----------------------------------------------------------------------------------------

/-- A normalized step appends precisely the mapped raw batch to flattened prior output.
Witness: an empty raw batch normalizes to empty output; the nonempty branch appends one
batch whose flattening is exactly its mapped events. No batch boundary is changed.
-/
theorem normalizedStep_flatten (acc : NormalizedAcc) (batch : List GraphEvent)
    : (normalizedStep acc batch).2.2.flatten
      = acc.2.2.flatten
        ++ (acc.2.1.normalizeBatch (acc.1.handleGraphEvents batch).2).2 := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  dsimp only [normalizedStep]
  split
  · rename_i empty
    rw [List.isEmpty_iff.mp empty]
    simp [IncrementalPublisher.normalizeBatch]
  · simp

/-- Whole normalized replay supplies one inventory for freshness, provenance, and every
task-produced stream carrier's earlier producer. Witness: each actual batch contributes its
joint raw ledger; normalization keeps carrier value counts; batch concatenation preserves
the very same occurrence labels. All queue-state premises are derived from initialization
and valid source input, without output admission or additional host assumptions.
-/
theorem createWorkQueue_runNormalized_streamReleasePublications {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    : ∃ published : List ObjectPublication,
        published.map (fun publication => publication.2)
          = ((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
              normalizedObjectValues
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.PublicationInventory
            (ObjectValueFrom batches.flatten) published
        ∧ NormalizedStreamReleasePublications work published
            ((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (before : List GraphEvent) (published : List ObjectPublication)
      (inventory : acc.1.PublicationInventory (ObjectValueFrom before) published)
      (settled : acc.1.ChildStreamsSettled) (links : acc.1.ChildStreamsMatchWork work)
      (values : published.map (fun publication => publication.2)
        = acc.2.2.flatten.flatMap normalizedObjectValues)
      (supported : NormalizedStreamReleasePublications work published acc.2.2.flatten)
      (valid : ValidGraphEvents work (before ++ more.flatten))
      : ∃ final : List ObjectPublication,
          final.map (fun publication => publication.2)
            = (more.foldl normalizedStep acc).2.2.flatten.flatMap normalizedObjectValues
          ∧ (more.foldl normalizedStep acc).1.PublicationInventory
              (ObjectValueFrom (before ++ more.flatten)) final
          ∧ NormalizedStreamReleasePublications work final
              (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc before published with
    | nil =>
        refine ⟨published, values, ?_, supported⟩
        simpa only [List.flatten_nil, List.append_nil, List.foldl_nil] using inventory
    | cons batch rest ih =>
        have firstPrefix : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
          ⟨rest.flatten, by simp [List.append_assoc]⟩
        have firstValid := valid.prefix firstPrefix
        obtain ⟨added, exactValues, current, releaseSupport⟩ :=
          inventory.handleGraphEvents_streamRelease settled links generated batch firstValid
        have nextInventory : (normalizedStep acc batch).1.PublicationInventory
            (ObjectValueFrom (before ++ batch)) (published ++ added) := by
          rw [normalizedStep_queue]
          exact current
        have nextSettled : (normalizedStep acc batch).1.ChildStreamsSettled := by
          rw [normalizedStep_queue]
          exact settled.handleGraphEvents batch
        have nextLinks : (normalizedStep acc batch).1.ChildStreamsMatchWork work := by
          rw [normalizedStep_queue]
          exact links.handleGraphEvents batch (fun event member =>
            firstValid.event_matches (List.mem_append_right before member))
        have nextValues : (published ++ added).map (fun publication => publication.2)
            = (normalizedStep acc batch).2.2.flatten.flatMap normalizedObjectValues := by
          rw [normalizedStep_objectValues, List.map_append, values]
          exact congrArg (acc.2.2.flatten.flatMap normalizedObjectValues ++ ·) exactValues
        have nextSupport : NormalizedStreamReleasePublications work (published ++ added)
            (normalizedStep acc batch).2.2.flatten := by
          rw [normalizedStep_flatten]
          exact supported.append (releaseSupport.normalizeBatch acc.2.1) values
        obtain ⟨final, finalValues, finalInventory, finalSupport⟩ :=
          ih _ (before ++ batch) (published ++ added) nextInventory nextSettled nextLinks
            nextValues nextSupport
            (by simpa only [List.flatten_cons, List.append_assoc] using valid)
        refine ⟨final, finalValues, ?_, finalSupport⟩
        simpa only [List.flatten_cons, List.append_assoc, List.foldl_cons]
          using finalInventory
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have initial : queue.PublicationInventory (ObjectValueFrom []) [] :=
    ⟨by simp, by simp, createWorkQueue_storedValues _ _⟩
  exact loop batches (queue, publisher, []) [] [] initial
    (createWorkQueue_childStreamsSettled _) (createWorkQueue_childStreamsMatchWork _ _)
    rfl (.nil work) valid

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
