import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValues

/-! Occurrence-indexed publication inventories through actual successful group flushes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Proof-only occurrence labels explain the values in actual raw queue output
-----------------------------------------------------------------------------------------

/-- A published object payload paired with its original execution-group occurrence.
The occurrence is proof evidence, not an added field in the implementation or wire format.
-/
abbrev ObjectPublication := Occurrence × ExecutionGroupValue

/-- Object values in one raw queue event; stream payloads and control events are excluded.
-/
abbrev _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.objectValues
  : WorkQueueEvent → List ExecutionGroupValue
  | .groupValues _ values => values
  | _ => []

/-- Label the nonempty stored values of selected nodes with their original occurrences. -/
def storedPublications (nodes : List TaskNode) : List ObjectPublication :=
  nodes.filterMap fun node => node.value.map (node.task.occurrence, ·)

/-- Erasing the occurrence labels recovers the exact selected payloads.
Witness: each node contributes either no value or its unchanged stored value. -/
theorem storedPublications_values (nodes : List TaskNode)
    : (storedPublications nodes).map Prod.snd = nodes.filterMap TaskNode.value := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      cases value : node.value with
      | none => simpa [storedPublications, value] using ih
      | some data => simpa [storedPublications, value] using congrArg (data :: ·) ih

/-- Every labelled publication identifies a selected node with that exact stored value.
Witness: filter-map membership, followed by the node's optional-value case. -/
theorem storedPublications_member {nodes : List TaskNode}
    {publication : ObjectPublication} (member : publication ∈ storedPublications nodes)
    : ∃ node ∈ nodes,
        node.task.occurrence = publication.1 ∧ node.value = some publication.2 := by
  obtain ⟨node, selected, same⟩ := List.mem_filterMap.mp member
  cases value : node.value with
  | none => simp [value] at same
  | some data =>
      simp only [value, Option.map_some, Option.some.injEq] at same
      exact ⟨node, selected, congrArg Prod.fst same,
        (congrArg (fun pair : ObjectPublication => some pair.2) same) ▸ value⟩

/-- Dropping nodes without values preserves occurrence uniqueness.
Witness: induction over the selected list and its duplicate-free occurrence projection. -/
theorem storedPublications_unique {nodes : List TaskNode}
    (unique : (nodes.map (fun node => node.task.occurrence)).Nodup)
    : ((storedPublications nodes).map Prod.fst).Nodup := by
  induction nodes with
  | nil => simp [storedPublications]
  | cons node rest ih =>
      obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
      cases value : node.value with
      | none => simpa [storedPublications, value] using ih restUnique
      | some data =>
          simp only [storedPublications, List.filterMap_cons, value, Option.map_some,
            List.map_cons]
          change (node.task.occurrence :: (storedPublications rest).map Prod.fst).Nodup
          refine List.nodup_cons.mpr ⟨?_, ih restUnique⟩
          intro member
          obtain ⟨publication, selected, same⟩ := List.mem_map.mp member
          obtain ⟨other, otherMember, occurrence, _⟩ := storedPublications_member selected
          exact fresh (List.mem_map.mpr ⟨other, otherMember, occurrence.trans same⟩)

/-- Published occurrences are distinct, and stored values exclude every published one.
The supplied property records source provenance for both stored and published payloads.
This inventory is proof evidence over output history, not executable queue state. -/
structure State.PublicationInventory (queue : State)
    (property : Occurrence → ExecutionGroupValue → Prop)
    (published : List ObjectPublication)
    : Prop where
  unique : (published.map Prod.fst).Nodup
  provenance : ∀ publication ∈ published, property publication.1 publication.2
  stored
    : queue.StoredValuesSatisfy
        (fun occurrence value =>
          property occurrence value ∧ occurrence ∉ published.map Prod.fst)

/-- Enlarging the allowed source evidence does not change publication freshness.
Witness: weaken provenance in both parts of the same inventory. -/
theorem State.PublicationInventory.mono {queue : State} {before after published}
    (inventory : queue.PublicationInventory before published)
    (weaken : ∀ occurrence value, before occurrence value → after occurrence value)
    : queue.PublicationInventory after published :=
  ⟨
    inventory.unique,
    fun publication member => weaken _ _ (inventory.provenance publication member),
    inventory.stored.mono (fun _ _ known => ⟨weaken _ _ known.1, known.2⟩)
  ⟩

/-- Updating group counters leaves the publication ledger and stored-value evidence intact.
Witness: group updates do not modify task nodes or the proof-only publication sequence. -/
theorem State.PublicationInventory.putGroupNode {queue : State} {property published}
    (inventory : queue.PublicationInventory property published) (updated : GroupNode)
    : (queue.putGroupNode updated).PublicationInventory property published :=
  ⟨inventory.unique, inventory.provenance, inventory.stored.putGroupNode updated⟩

-----------------------------------------------------------------------------------------
-- A flush extends the inventory once, then removes the selected stored occurrences
-----------------------------------------------------------------------------------------

/-- A specified flush selection extends the inventory by precisely its stored occurrences.
Witness: selected-node uniqueness, exact value erasure, and removal from the residual map.
Keeping this selection explicit lets release proofs share the same occurrence labels.
-/
theorem State.PublicationInventory.finishGroupSuccess_selected {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (group : GroupNode) (selected : List TaskNode)
    (unique : (selected.map (fun node => node.task.occurrence)).Nodup)
    (known
      : ∀ node ∈ selected, node ∈ queue.taskNodes ∧ node.task.occurrence ∈ group.tasks)
    (events
      : (queue.finishGroupSuccess group).2.1
        = (if (selected.filterMap TaskNode.value).isEmpty then
              []
            else
              [.groupValues group.group.node (selected.filterMap TaskNode.value)])
          ++ [.groupSuccess group.group.node
                (queue.finishGroupSuccess group).2.2.newGroups
                (queue.finishGroupSuccess group).2.2.newStreams])
    (retained : (queue.finishGroupSuccess group).1.taskNodes.Subset queue.taskNodes)
    (absent
      : ∀ node ∈ selected,
        ∀ retained ∈ (queue.finishGroupSuccess group).1.taskNodes,
          retained.task.occurrence ≠ node.task.occurrence)
    : (storedPublications selected).map Prod.snd
        = (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.objectValues
      ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
          (published ++ storedPublications selected) := by
  let added := storedPublications selected
  have addedKnown (publication : ObjectPublication) (member : publication ∈ added)
      : property publication.1 publication.2 ∧ publication.1 ∉ published.map Prod.fst := by
    obtain ⟨node, selectedNode, occurrence, value⟩ := storedPublications_member member
    simpa only [occurrence] using inventory.stored node (known node selectedNode).1 _ value
  refine ⟨?_, ?_⟩
  · rw [events]
    change (storedPublications selected).map Prod.snd = _
    rw [storedPublications_values]
    split
    · rename_i empty
      simpa only [List.flatMap_append, List.flatMap_nil, List.flatMap_singleton,
        WorkQueueEvent.objectValues, List.nil_append] using List.isEmpty_iff.mp empty
    · simp [WorkQueueEvent.objectValues]
  · refine ⟨?_, ?_, ?_⟩
    · rw [List.map_append]
      apply List.nodup_append.mpr
      refine ⟨inventory.unique, storedPublications_unique unique, ?_⟩
      intro earlier earlierMember later laterMember same
      obtain ⟨publication, member, equal⟩ := List.mem_map.mp laterMember
      exact (addedKnown publication member).2 (equal.symm ▸ same ▸ earlierMember)
    · intro publication member
      rcases List.mem_append.mp member with old | new
      · exact inventory.provenance publication old
      · exact (addedKnown publication new).1
    · intro node member value stored
      obtain ⟨source, oldFresh⟩ := inventory.stored node (retained member) value stored
      refine ⟨source, ?_⟩
      intro already
      rw [List.map_append] at already
      rcases List.mem_append.mp already with old | new
      · exact oldFresh old
      · obtain ⟨publication, publicationMember, same⟩ := List.mem_map.mp new
        obtain ⟨selectedNode, selectedMember, occurrence, _⟩ :=
          storedPublications_member publicationMember
        exact absent selectedNode selectedMember node member (same.symm.trans occurrence.symm)

/-- Successful group cleanup adds exactly its fresh object publications to the inventory.
Witness: choose the executable flush selection and apply its occurrence-labelled ledger.
Both old and new published occurrences are excluded from every remaining stored value.
-/
theorem State.PublicationInventory.finishGroupSuccess {queue : State} {property published}
    (inventory : queue.PublicationInventory property published) (group : GroupNode)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added) := by
  obtain ⟨selected, unique, known, events, retained, absent⟩ :=
    queue.finishGroupSuccess_publications group
  exact ⟨storedPublications selected,
    inventory.finishGroupSuccess_selected group selected unique known events retained absent⟩

/-- Recursive draining adds exactly its fresh object publications to the inventory.
Witness: each successful flush removes its selected occurrences before later drains;
cached-failure closures emit no object values and cannot restore any stored value.
-/
theorem State.PublicationInventory.drainReadyGroups {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd = queue.drainReadyGroups.2.flatMap WorkQueueEvent.objectValues
        ∧ queue.drainReadyGroups.1.PublicationInventory property
            (published ++ added) := by
  have loop (fuel : Nat) (current : State) (priorPublished : List ObjectPublication)
      (prior : current.PublicationInventory property priorPublished)
      : ∃ added : List ObjectPublication,
          added.map Prod.snd
            = (State.drainReadyGroups.go fuel current).2.flatMap WorkQueueEvent.objectValues
          ∧ (State.drainReadyGroups.go fuel current).1.PublicationInventory property
              (priorPublished ++ added) := by
    induction fuel generalizing current priorPublished with
    | zero =>
        exact ⟨
          [],
          rfl,
          by simpa only [State.drainReadyGroups.go,
            List.append_nil] using prior
        ⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨[], rfl, by simpa using prior⟩
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              dsimp only
              obtain ⟨first, firstValues, flushed⟩ := prior.finishGroupSuccess node
              obtain ⟨later, laterValues, final⟩ := ih _ _
                ⟨flushed.unique, flushed.provenance,
                  flushed.stored.startNewWork (current.finishGroupSuccess node).2.2⟩
              refine ⟨first ++ later, ?_, ?_⟩
              · simp only [List.map_append, List.flatMap_append, firstValues, laterValues]
              · simpa only [List.append_assoc] using final
          | some errors =>
              dsimp only
              obtain ⟨added, values, final⟩ := ih _ _
                ⟨prior.unique, prior.provenance, prior.stored.removeGroup _⟩
              refine ⟨added, ?_, final⟩
              simpa only [State.finishGroupFailure, List.flatMap_append,
                List.flatMap_singleton, WorkQueueEvent.objectValues, List.nil_append]
                using values
  exact loop _ queue published inventory

-----------------------------------------------------------------------------------------
-- The single-pass success handler preserves freshness across all contributor flushes
-----------------------------------------------------------------------------------------

/-- One contributor step extends the exact output witness and publication inventory.
Witness: unchanged branches retain it; a flushing branch appends its new selected values.
The next contributor sees those occurrences already excluded from stored values. -/
theorem successGroupStep_publications {property published}
    (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
    {added : List ObjectPublication}
    (values : added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues)
    (inventory : acc.1.PublicationInventory property (published ++ added))
    : ∃ next : List ObjectPublication,
        next.map Prod.snd
          = (successGroupStep acc group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (successGroupStep acc group).1.PublicationInventory property
            (published ++ next) := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨added, values, inventory⟩
  · rename_i owner found
    split
    · have updated := inventory.putGroupNode { owner with pending := owner.pending - 1 }
      obtain ⟨extra, exactValues, nextInventory⟩ := updated.finishGroupSuccess
        { owner with pending := owner.pending - 1 }
      refine ⟨added ++ extra, ?_, ?_⟩
      · simp only [List.map_append, List.flatMap_append, values, exactValues]
      · simpa only [List.append_assoc] using nextInventory
    · exact ⟨added, values, inventory.putGroupNode _⟩

/-- A task success emits an occurrence-unique sequence fresh against all prior publications.
Witness: install the fresh input and carry the inventory through integration, contributor
flushes, and the final recursive drain after activating released work. -/
theorem State.PublicationInventory.taskSuccess {queue : State} {property published}
    (inventory : queue.PublicationInventory property published) (occurrence : Occurrence)
    (result : TaskResult) (allowed : property occurrence result.value)
    (fresh : occurrence ∉ published.map Prod.fst)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.taskSuccess occurrence result).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.taskSuccess occurrence result).1.PublicationInventory property
            (published ++ added) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      refine ⟨[], rfl, ?_⟩
      simpa only [List.append_nil] using inventory
  | some node =>
      have equal := (State.taskNode?_some found).2
      have installed := inventory.stored.putTaskNode { node with value := some result.value } (by
        intro value same
        cases same
        simpa only [equal] using And.intro allowed fresh)
      have integrated := installed.maybeIntegrateWork result.work (some occurrence)
      have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
          (prior : ∃ added : List ObjectPublication,
            added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues
            ∧ acc.1.PublicationInventory property (published ++ added))
          : ∃ added : List ObjectPublication,
            added.map Prod.snd = (groups.foldl successGroupStep acc).2.1.flatMap
              WorkQueueEvent.objectValues
            ∧ (groups.foldl successGroupStep acc).1.PublicationInventory property
              (published ++ added) := by
        induction groups generalizing acc with
        | nil => exact prior
        | cons group rest ih =>
            obtain ⟨added, values, next⟩ := prior
            exact ih _ (successGroupStep_publications acc group values next)
      obtain ⟨added, values, final⟩ := loop node.task.groups (_, [], {})
        ⟨[], rfl, by simpa only [List.append_nil] using
          State.PublicationInventory.mk inventory.unique inventory.provenance integrated⟩
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · refine ⟨[], rfl, ?_⟩
        simpa only [List.append_nil]
          using State.PublicationInventory.mk inventory.unique inventory.provenance
            (inventory.stored.removeTask occurrence)
      let released := node.task.groups.foldl successGroupStep
        (((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1, [], {})
      have activated := State.PublicationInventory.mk final.unique final.provenance
        (final.stored.startNewWork released.2.2)
      obtain ⟨later, laterValues, drained⟩ := activated.drainReadyGroups
      refine ⟨added ++ later, ?_, ?_⟩
      · simp only [List.map_append, List.flatMap_append, values, laterValues]
        rfl
      · simpa only [List.append_assoc] using drained

-----------------------------------------------------------------------------------------
-- Failure controls preserve the inventory; stream arrivals can drain stored object values
-----------------------------------------------------------------------------------------

/-- Task failure emits only group-failure notices, never object values.
Witness: the owner fold appends failure notices or silently updates cached errors. -/
theorem State.taskFailure_objectValues (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).2.flatMap WorkQueueEvent.objectValues
      = [] := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.key with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.key then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else
          (acc.1.putGroupNode
            { node with pending := node.pending - 1
                        failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : (groups.foldl step acc).2.flatMap WorkQueueEvent.objectValues =
          acc.2.flatMap WorkQueueEvent.objectValues := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        unfold step
        split
        · rfl
        · split
          · simp [State.finishGroupFailure, List.flatMap_append, WorkQueueEvent.objectValues]
          · rfl
  unfold State.taskFailure
  split
  · rfl
  · split
    · rfl
    exact loop _ (_, [])

/-- Stream-item arrival can publish stored object values through its final ready-group drain.
Witness: item integration preserves the inventory; draining then supplies exact, fresh
occurrence labels for every object value after the leading stream-item event.
-/
theorem State.PublicationInventory.streamItems {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.streamItems stream items).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.streamItems stream items).1.PublicationInventory property
            (published ++ added) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (rest : List StreamItem)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.PublicationInventory property published)
      : (rest.foldl step acc).1.PublicationInventory property published := by
    induction rest generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih _ ⟨prior.unique, prior.provenance,
          ((prior.stored.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _⟩
  have folded := loop items (queue, [], [], []) inventory
  unfold State.streamItems
  split
  · exact ⟨[], rfl, by simpa using inventory⟩
  · simpa only [List.flatMap_cons, WorkQueueEvent.objectValues, List.nil_append]
      using folded.drainReadyGroups

/-- Every event extends the publication inventory with exactly its emitted object values.
Witness: success and item handlers extend the ledger through their final drains; failure
and stream-close controls preserve it. A new success must be fresh against prior output. -/
theorem State.PublicationInventory.handleGraphEvent {queue : State} {property published}
    (inventory : queue.PublicationInventory property published) (event : GraphEvent)
    (allowed
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → property occurrence result.value ∧ occurrence ∉ published.map Prod.fst)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvent event).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvent event).1.PublicationInventory property
            (published ++ added) := by
  have preserved := inventory.stored.handleGraphEvent event allowed
  cases event with
  | taskSuccess occurrence result =>
      exact inventory.taskSuccess occurrence result (allowed _ _ rfl).1 (allowed _ _ rfl).2
  | taskFailure occurrence errors =>
      exact ⟨
        [],
        (queue.taskFailure_objectValues occurrence errors).symm,
        by
          simpa only [List.append_nil]
            using State.PublicationInventory.mk inventory.unique inventory.provenance
              preserved
      ⟩
  | streamItems stream items =>
      exact inventory.streamItems stream items
  | streamSuccess stream =>
      refine ⟨
        [],
        ?_,
        by
          simpa only [List.append_nil]
            using State.PublicationInventory.mk inventory.unique inventory.provenance
              preserved
      ⟩
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> rfl
  | streamFailure stream errors =>
      refine ⟨
        [],
        ?_,
        by
          simpa only [List.append_nil]
            using State.PublicationInventory.mk inventory.unique inventory.provenance
              preserved
      ⟩
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
