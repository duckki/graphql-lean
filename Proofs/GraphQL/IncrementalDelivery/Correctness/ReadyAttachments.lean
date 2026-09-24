import Proofs.GraphQL.IncrementalDelivery.Correctness.AttachmentSlices
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourcePublicationCoverage

/-! Producer-closed publication sets make every ready source task's parent available. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open SourceReconstruction SourceAttachments

/-- Object patches require an existing object; streamed items require an existing list. -/
def SourceTask.attachment (task : SourceTask) : TypedResponse.Entry :=
  match task.payload with
  | .object path _ => (path, .object)
  | .item node _ => (node.path, .list)

/-- A task without a producer is ready; otherwise its producer must already be
published.
-/
def ProducerReady (published : WorkScheduler.Occurrence → Prop)
    (producer : Option WorkScheduler.Occurrence)
    : Prop :=
  ∀ parent, producer = some parent → published parent

/-- A published labelled task exposes its inherited context and its own payload entries.
Witness: producer closure plus membership of all published entries in available data.
-/
theorem published_context {inventory : List SourceTask} {available ambient}
    {published : WorkScheduler.Occurrence → Prop} {task : SourceTask}
    (member : task ∈ inventory)
    (closed
      : ∀ task ∈ inventory,
          published task.occurrence → ProducerReady published task.producer)
    (delivered
      : ∀ task ∈ inventory, published task.occurrence → task.entries.Subset available)
    (context : ProducerReady published task.producer → ambient.Subset available)
    (ready : ProducerReady published (some task.occurrence))
    : (ambient ++ task.entries).Subset available := by
  have done := ready task.occurrence rfl
  intro entry memberEntry
  rcases List.mem_append.mp memberEntry with prior | fresh
  · exact context (closed task member done) prior
  · exact delivered task member done fresh

mutual
  /-- Every ready labelled task has its parent tag in available data. Witness: structural
  attachment certificates, producer closure, and published ancestor payloads.
  -/
  theorem sourceTasks_readyAttached {inventory : List SourceTask}
      {published : WorkScheduler.Occurrence → Prop} {available : List TypedResponse.Entry}
      (closed
        : ∀ task ∈ inventory,
            published task.occurrence → ProducerReady published task.producer)
      (delivered
        : ∀ task ∈ inventory, published task.occurrence → task.entries.Subset available)
      (address producer cursors work) {ambient : List TypedResponse.Entry}
      (members : (sourceTasks address producer cursors work).Subset inventory)
      (success : WorkSuccess work)
      (attached
        : WorkAttached ambient work
            (entryPaths
              ((sourceTasks address producer cursors work).map SourceTask.entries)))
      (context : ProducerReady published producer → ambient.Subset available)
      : ∀ task ∈ sourceTasks address producer cursors work,
          ProducerReady published task.producer → task.attachment ∈ available := by
    cases work with
    | empty => simp [sourceTasks]
    | combine left right =>
        generalize equal : entryPaths ((sourceTasks address producer cursors
          (.combine left right)).map SourceTask.entries) = slices at attached
        cases attached with
        | combine al ar =>
            simp only [sourceTasks, List.map_append, entryPaths] at equal
            obtain ⟨leftEq, rightEq⟩ := List.append_inj equal (by
              simpa only [List.length_map] using
                (sourceTasks_entries (address ++ [0]) producer cursors left).attached_length al)
            intro task member ready
            rcases List.mem_append.mp member with first | second
            · exact sourceTasks_readyAttached closed delivered _ _ _ left
                (fun _ member => members (List.mem_append_left _ member)) success.1
                (by simpa only [entryPaths, leftEq] using al) context task first ready
            · exact sourceTasks_readyAttached closed delivered _ _ _ right
                (fun _ member => members (List.mem_append_right _ member)) success.2
                (by simpa only [entryPaths, rightEq] using ar) context task second ready
    | executionGroup groups path result children =>
        simp only [sourceTasks, List.map_cons, entryPaths,
          SourceTask.entries, result_fields_paths] at attached
        cases attached with
        | executionGroup parent childrenAttached =>
            intro task member ready
            rcases List.mem_cons.mp member with rfl | child
            · exact context ready parent
            · apply sourceTasks_readyAttached closed delivered _ _ _ children
                (fun _ member => members (List.mem_cons_of_mem _ member)) success.2
                childrenAttached ?_ task child ready
              exact published_context (members (by simp [sourceTasks])) closed delivered context
    | stream node items =>
        generalize equal : entryPaths ((sourceTasks address producer cursors
          (.stream node items)).map SourceTask.entries) = slices at attached
        cases attached with
        | @stream _ _ _ other _ parent itemAttached =>
            have same : ItemsAttached ambient node.path
                ((ResponsePositions.cursorAt cursors node.path).getD 0) items
                (entryPaths ((sourceTasks address producer cursors (.stream node items)).map
                  SourceTask.entries)) := by
              cases items with
              | nil => exact .nil
              | cons head rest =>
                  have indices := ItemsAttached.index_eq
                    (sourceItemTasks_entries address producer node _ 0 (head :: rest))
                    success (equal ▸ itemAttached) (by simp)
                  subst other
                  exact equal ▸ itemAttached
            exact sourceItemTasks_readyAttached closed delivered address producer node _ 0
              items members success same context parent
  termination_by sizeOf work

  /-- Stream item parents use the ambient list, while descendants use the published
  item's added entries. Witness: item-list descent with exact attachment offsets.
  -/
  theorem sourceItemTasks_readyAttached {inventory : List SourceTask}
      {published : WorkScheduler.Occurrence → Prop} {available : List TypedResponse.Entry}
      (closed
        : ∀ task ∈ inventory,
            published task.occurrence → ProducerReady published task.producer)
      (delivered
        : ∀ task ∈ inventory, published task.occurrence → task.entries.Subset available)
      (address producer node index ordinal items) {ambient : List TypedResponse.Entry}
      (members
        : (sourceItemTasks address producer node index ordinal items).Subset inventory)
      (success : ItemsSuccess items)
      (attached
        : ItemsAttached ambient node.path index items
            (entryPaths
              ((sourceItemTasks address producer node index ordinal items).map
                SourceTask.entries)))
      (context : ProducerReady published producer → ambient.Subset available)
      (parent : (node.path, TypedResponse.Atom.list) ∈ ambient)
      : ∀ task ∈ sourceItemTasks address producer node index ordinal items,
          ProducerReady published task.producer → task.attachment ∈ available := by
    cases items with
    | nil => simp [sourceItemTasks]
    | cons head rest =>
        cases equal : head with
        | mk result children =>
            simp only [equal] at attached members success
            generalize slicesEq : entryPaths ((sourceItemTasks address producer node index
              ordinal ((result, children) :: rest)).map SourceTask.entries) = slices at attached
            cases attached with
            | cons childAttached tailAttached =>
                simp only [sourceItemTasks, List.map_cons, List.map_append, entryPaths,
                  SourceTask.entries, result_value_paths, List.cons.injEq] at slicesEq
                obtain ⟨childEq, tailEq⟩ := List.append_inj slicesEq.2 (by
                  simpa only [List.length_map] using
                    (sourceTasks_entries _ _ _ children).attached_length childAttached)
                intro task member ready
                rcases List.mem_cons.mp member with rfl | member
                · exact context ready parent
                · rcases List.mem_append.mp member with child | tail
                  · apply sourceTasks_readyAttached closed delivered _ _ _ children
                      (fun _ member => members (List.mem_cons_of_mem _
                        (List.mem_append_left _ member))) success.2.1
                      (by simpa only [entryPaths, childEq] using childAttached) ?_ task child ready
                    exact published_context (members (by simp [sourceItemTasks]))
                      closed delivered context
                  · exact sourceItemTasks_readyAttached closed delivered address producer node
                      (index + 1) (ordinal + 1) rest
                      (fun _ member => members (List.mem_cons_of_mem _
                        (List.mem_append_right _ member))) success.2.2
                      (by simpa only [entryPaths, tailEq] using tailAttached)
                      context parent task tail ready
  termination_by sizeOf items
  decreasing_by all_goals subst_vars; simp_wf; omega
end

end GraphQL.IncrementalDelivery.Correctness
