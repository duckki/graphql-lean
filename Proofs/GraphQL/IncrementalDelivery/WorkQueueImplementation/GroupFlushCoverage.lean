import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationInventory

/-! Successful group flushing accounts for every available stored membership. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- One complete selection supplies both publication provenance and coverage
-----------------------------------------------------------------------------------------

/-- Every findable membership with a stored value is published before the group's closure.
Witness: the complete executable selection labels each stored value with its occurrence.
The same labels extend the existing freshness/provenance inventory; no second matching
is chosen. Missing nodes are deliberately not treated as published or cancelled here.
-/
theorem State.PublicationInventory.finishGroupSuccess_coverage {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (group : GroupNode)
    : ∃ (added : List ObjectPublication) (before : List WorkQueueEvent),
        (queue.finishGroupSuccess group).2.1
          = before
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ added.map Prod.snd = before.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ (∀ occurrence ∈ group.tasks,
            ∀ node value,
              queue.taskNode? occurrence = some node
              → node.value = some value
              → (occurrence, value) ∈ added)
        ∧ (∀ occurrence ∈ group.tasks,
            ∀ node,
              queue.taskNode? occurrence = some node
              → ∀ retained ∈ (queue.finishGroupSuccess group).1.taskNodes,
                  retained.task.occurrence ≠ occurrence) := by
  obtain ⟨selected, unique, known, events, retained, absent, _, covered, _⟩ :=
    queue.finishGroupSuccess_completeSelection group
  obtain ⟨values, next⟩ := inventory.finishGroupSuccess_selected group selected unique known
    events retained absent
  let before : List WorkQueueEvent :=
    if (selected.filterMap TaskNode.value).isEmpty then []
    else [.groupValues group.group.node (selected.filterMap TaskNode.value)]
  refine ⟨storedPublications selected, before, events, ?_, next, ?_, ?_⟩
  · rw [events, List.flatMap_append] at values
    simpa only [List.flatMap_singleton, WorkQueueEvent.objectValues, List.append_nil]
      using values
  · intro occurrence member node value found stored
    apply List.mem_filterMap.mpr
    refine ⟨node, covered occurrence member node found, ?_⟩
    simp only [stored, Option.map_some, (State.taskNode?_some found).2]
  · intro occurrence member node found other live
    simpa only [(State.taskNode?_some found).2]
      using absent node (covered occurrence member node found) other live

/-- An active group's buffered contributors all publish before its completion event.
Witness: active task links place each contributor in the closing membership list, and the
complete flush selects its unchanged stored value. Links and active-node membership are
internal queue facts to obtain at the actual flush boundary, not new host-source laws.
-/
theorem State.PublicationInventory.finishGroupSuccess_contributors {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (links : queue.ActiveTaskLinks) (group : GroupNode)
    (live : group ∈ queue.groupNodes) (active : group.group.node.ref ∈ queue.rootGroups)
    : ∃ (added : List ObjectPublication) (before : List WorkQueueEvent),
        (queue.finishGroupSuccess group).2.1
          = before
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ added.map Prod.snd = before.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → group.group.node.ref ∈ node.task.groups.map Execution.DeliveryNode.ref
            → (occurrence, value) ∈ added) := by
  obtain ⟨added, before, output, values, next, covered, _⟩ :=
    inventory.finishGroupSuccess_coverage group
  refine ⟨added, before, output, values, next, ?_⟩
  intro occurrence node value found stored contributor
  have known := State.taskNode?_some found
  have member : occurrence ∈ group.tasks :=
    known.2 ▸ links node known.1 group live active contributor
  exact covered occurrence member node value found stored

/-- A membership already published, or still holding a value, is covered by this closure.
Witness: retain earlier occurrence labels and use complete flush coverage for live values.
This is a local accounting reduction: replay must establish the supplied alternatives,
including any cancellation case, before applying it to all structural contributors.
-/
theorem State.PublicationInventory.finishGroupSuccess_accountsMemberships {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (group : GroupNode)
    (available
      : ∀ occurrence ∈ group.tasks,
          occurrence ∈ published.map Prod.fst
          ∨ ∃ node value,
              queue.taskNode? occurrence = some node ∧ node.value = some value)
    : ∃ (added : List ObjectPublication) (before : List WorkQueueEvent),
        (queue.finishGroupSuccess group).2.1
          = before
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ added.map Prod.snd = before.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ group.tasks.Subset ((published ++ added).map Prod.fst) := by
  obtain ⟨added, before, output, values, next, covered, _⟩ :=
    inventory.finishGroupSuccess_coverage group
  refine ⟨added, before, output, values, next, ?_⟩
  intro occurrence member
  rw [List.map_append]
  rcases available occurrence member with earlier | stored
  · exact List.mem_append_left _ earlier
  · obtain ⟨node, value, found, stored⟩ := stored
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨(occurrence, value), covered occurrence member node value found
        stored, rfl⟩)

/-- Successful closure either publishes a stored occurrence or preserves its exact node.
Witness: members are covered by the same complete labelled selection; nonmembers retain
their lookup across flushing and pruning. Values, errors, and contributor metadata are
preserved together. This conservation fact needs no source or healthy-counter premise.
-/
theorem State.PublicationInventory.finishGroupSuccess_conserves {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (group : GroupNode)
    : ∃ (added : List ObjectPublication) (before : List WorkQueueEvent),
        (queue.finishGroupSuccess group).2.1
          = before
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ added.map Prod.snd = before.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (occurrence, value) ∈ added
              ∨ (queue.finishGroupSuccess group).1.taskNode? occurrence = some node) := by
  obtain ⟨added, before, output, values, next, covered, _⟩ :=
    inventory.finishGroupSuccess_coverage group
  refine ⟨added, before, output, values, next, ?_⟩
  intro occurrence node value found stored
  by_cases member : occurrence ∈ group.tasks
  · exact Or.inl (covered occurrence member node value found stored)
  · exact Or.inr ((queue.finishGroupSuccess_lookup_unselected group member).trans found)

-----------------------------------------------------------------------------------------
-- Shared-owner success processing cannot lose a stored payload between flushes
-----------------------------------------------------------------------------------------

/-- One contributor step preserves both the publication ledger and every earlier value.
Witness: counter-only branches retain the node; a flush either publishes it or leaves its
exact lookup intact. Occurrence labels accumulate in the actual single-pass output order.
-/
private theorem successGroupStep_conserves {property published} (original : State)
    (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
    {added : List ObjectPublication}
    (values : added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues)
    (inventory : acc.1.PublicationInventory property (published ++ added))
    (conserved
      : ∀ occurrence node value,
          original.taskNode? occurrence = some node
          → node.value = some value
          → (occurrence, value) ∈ added ∨ acc.1.taskNode? occurrence = some node)
    : ∃ next : List ObjectPublication,
        next.map Prod.snd
          = (successGroupStep acc group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (successGroupStep acc group).1.PublicationInventory property (published ++ next)
        ∧ (∀ occurrence node value,
            original.taskNode? occurrence = some node
            → node.value = some value
            → (occurrence, value) ∈ next
              ∨ (successGroupStep acc group).1.taskNode? occurrence = some node) := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨added, values, inventory, conserved⟩
  · rename_i owner found
    split
    · have updated := inventory.putGroupNode { owner with pending := owner.pending - 1 }
      obtain ⟨extra, before, output, extraValues, nextInventory, nextConserved⟩ :=
        updated.finishGroupSuccess_conserves { owner with pending := owner.pending - 1 }
      refine ⟨added ++ extra, ?_, ?_, ?_⟩
      · simp only [List.map_append, List.flatMap_append, output,
          List.flatMap_singleton, WorkQueueEvent.objectValues, List.append_nil,
          values, extraValues]
      · simpa only [List.append_assoc] using nextInventory
      · intro occurrence node value lookup stored
        rcases conserved occurrence node value lookup stored with earlier | retained
        · exact Or.inl (List.mem_append_left _ earlier)
        · rcases nextConserved occurrence node value retained stored with now | still
          · exact Or.inl (List.mem_append_right _ now)
          · exact Or.inr still
    · exact ⟨added, values, inventory.putGroupNode _, conserved⟩

/-- The full single-pass contributor fold publishes or retains every initial stored value.
Witness: iterate the same conservation/inventory construction over actual contributor
order, including absent owners and shared-task removal by an earlier owner. The resulting
labels are occurrence-unique by the retained inventory; no counter or source premise is
assumed. Integration, failed cleanup, and the subsequent recursive drain are separate.
-/
theorem State.PublicationInventory.successGroupFold_conserves {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (groups : List Execution.DeliveryNode)
    : let result := groups.foldl successGroupStep (queue, [], {})
      ∃ added : List ObjectPublication,
        added.map Prod.snd = result.2.1.flatMap WorkQueueEvent.objectValues
        ∧ result.1.PublicationInventory property (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (occurrence, value) ∈ added
              ∨ result.1.taskNode? occurrence = some node) := by
  have loop (more : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork) (added : List ObjectPublication)
      (values : added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues)
      (current : acc.1.PublicationInventory property (published ++ added))
      (conserved
        : ∀ occurrence node value,
            queue.taskNode? occurrence = some node → node.value = some value
            → (occurrence, value) ∈ added ∨ acc.1.taskNode? occurrence = some node)
      : ∃ next : List ObjectPublication,
          next.map Prod.snd
            = (more.foldl successGroupStep acc).2.1.flatMap WorkQueueEvent.objectValues
          ∧ (more.foldl successGroupStep acc).1.PublicationInventory property
              (published ++ next)
          ∧ (∀ occurrence node value,
              queue.taskNode? occurrence = some node → node.value = some value
              → (occurrence, value) ∈ next
                ∨ (more.foldl successGroupStep acc).1.taskNode? occurrence = some node) := by
    induction more generalizing acc added with
    | nil => exact ⟨added, values, current, conserved⟩
    | cons group rest ih =>
        obtain ⟨next, output, retained, preserved⟩ :=
          successGroupStep_conserves queue acc group values current conserved
        exact ih _ next output retained preserved
  exact loop groups (queue, [], {}) [] rfl
    (by simpa only [List.append_nil] using inventory)
    (fun _ _ _ found _ => Or.inr found)

-----------------------------------------------------------------------------------------
-- An empty value prefix cannot silently discard a findable stored payload
-----------------------------------------------------------------------------------------

/-- A value-free successful flush had no stored value at any findable membership.
Witness: complete coverage would put that value in the exact emitted prefix, contradicting
its empty projection. This does not identify absent tasks with completed tasks.
-/
theorem State.finishGroupSuccess_noValues {queue : State} {group : GroupNode}
    (empty
      : (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.objectValues = [])
    {occurrence : Occurrence} (member : occurrence ∈ group.tasks) {node : TaskNode}
    (found : queue.taskNode? occurrence = some node)
    : node.value = none := by
  obtain ⟨selected, _, _, output, _, _, _, covered, _⟩ :=
    queue.finishGroupSuccess_completeSelection group
  have valuesEmpty : selected.filterMap TaskNode.value = [] := by
    rw [output] at empty
    split at empty
    · rename_i noValues
      exact List.isEmpty_iff.mp noValues
    · simpa [WorkQueueEvent.objectValues] using empty
  cases stored : node.value with
  | none => rfl
  | some value =>
      have included : value ∈ selected.filterMap TaskNode.value :=
        List.mem_filterMap.mpr ⟨node, covered occurrence member node found, stored⟩
      rw [valuesEmpty] at included
      cases included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
