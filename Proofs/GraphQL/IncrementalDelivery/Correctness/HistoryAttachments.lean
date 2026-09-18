import Proofs.GraphQL.IncrementalDelivery.Correctness.ReadyAttachments

/-! Every admitted value publication has its parent in previously published typed data. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open SourceReconstruction SourceAttachments

/-- Published tasks in any prefix have already-published producers. Witness: the
independent producer-order rule, transported through the prefix's lookup bound.
-/
theorem published_prefix_ready
    {work groups streams events matching failures cursors cut task}
    (explained : Explains work groups streams events matching failures)
    (member : task ∈ sourceTasks [] none cursors work)
    (published : Published matching (events.take cut) task.occurrence)
    : ProducerReady (Published matching (events.take cut)) task.producer := by
  obtain ⟨owners, known⟩ := sourceTasks_known .root cursors member
  obtain ⟨index, event, before, selected, value, same⟩ := published.before
  intro parent producer
  have located : TaskAt work (matching index) owners (some parent) task.payload := by
    simpa only [same, ← producer] using known
  obtain ⟨earlier, previous, less, atEarlier, isValue, matched⟩ :=
    explained.producer_before selected value located
  exact ⟨
    earlier,
    previous,
    (List.getElem?_take_of_lt (by omega)).trans atEarlier,
    isValue,
    matched
  ⟩

/-- A source label published before the cut belongs to the exact selected prefix list.
Witness: actual publication lookup and functional source occurrence lookup.
-/
theorem published_prefix_member {work events matching cursors cut task}
    (member : task ∈ sourceTasks [] none cursors work)
    (published : Published matching (events.take cut) task.occurrence)
    : task
      ∈ sourcePrefixTasks (sourceTasks [] none cursors work) matching events cut := by
  obtain ⟨index, event, before, selected, value, same⟩ := published.before
  exact sourcePrefixTasks_of_publication member selected value same.symm before

/-- Every ready task's attachment tag lies in the initial or previously published data.
Witness: producer-closed prefix publications discharge the structural attachment theorem.
-/
theorem history_ready_attachment
    {work groups streams events matching failures cursors cut initial}
    (explained : Explains work groups streams events matching failures)
    (success : WorkSuccess work)
    (attached
      : WorkAttached initial work
          (entryPaths ((sourceTasks [] none cursors work).map SourceTask.entries)))
    {task} (member : task ∈ sourceTasks [] none cursors work)
    (ready : ProducerReady (Published matching (events.take cut)) task.producer)
    : task.attachment
      ∈ initial
        ++ (sourcePrefixTasks (sourceTasks [] none cursors work) matching events
              cut).flatMap
            SourceTask.entries := by
  apply sourceTasks_readyAttached
    (fun task member published => published_prefix_ready explained member published)
    (fun task member published entry belongs => List.mem_append_right _
      (List.mem_flatMap.mpr ⟨task, published_prefix_member member published, belongs⟩))
    [] none cursors work (fun _ member => member) success attached
    (fun _ _ member => List.mem_append_left _ member) task member ready

/-- A supplied value event's exact labelled payload has an available attachment parent.
Witness: event readiness identifies the same producer as the structural source task.
-/
theorem history_publication_attachment
    {work groups streams events matching failures cursors cut initial task event}
    (explained : Explains work groups streams events matching failures)
    (success : WorkSuccess work)
    (attached
      : WorkAttached initial work
          (entryPaths ((sourceTasks [] none cursors work).map SourceTask.entries)))
    (member : task ∈ sourceTasks [] none cursors work)
    (selected : events[cut]? = some event) (value : IsValue event)
    (same : task.occurrence = matching cut)
    : task.attachment
      ∈ initial
        ++ (sourcePrefixTasks (sourceTasks [] none cursors work) matching events
              cut).flatMap
            SourceTask.entries := by
  apply history_ready_attachment explained success attached member
  obtain ⟨owners, known⟩ := sourceTasks_known .root cursors member
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  have allowed := (explained.2.2 cut event selected).publicationReady value
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)] at allowed
  obtain ⟨otherOwners, producer, payload, actual, ready⟩ := allowed
  have producerEq := (known.unique (same ▸ actual)).2.1
  exact fun parent equal => ready.2.2.1 parent (producerEq.symm.trans equal)

end GraphQL.IncrementalDelivery.Correctness
