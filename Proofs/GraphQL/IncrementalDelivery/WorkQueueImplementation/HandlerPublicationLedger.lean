import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureValueRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Source handlers retain one ledger for buffered closures and stream release. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful source settlement covers old values as well as its newly installed value
-----------------------------------------------------------------------------------------

/-- Successful input has one ledger covering both the input and prepared task maps.
Witness: source freshness separates every earlier stored value from the incoming task;
registration preserves those exact lookups before the joint release/drain certificate.
The prepared-state clause additionally covers the newly installed input value.
-/
theorem State.PublicationInventory.taskSuccess_bufferedCoverage {queue : State}
    {work before published settledTasks}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work settledTasks)
    (included : settledTasks.Subset (before.flatMap (fun event => event.identities.1)))
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (occurrence : Occurrence)
    (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (memberships : queue.GroupMembershipOrder)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.taskSuccess occurrence result).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.taskSuccess occurrence result).1.PublicationInventory
            (ObjectValueFrom (before ++ [.taskSuccess occurrence result]))
            (published ++ added)
        ∧ queue.BufferedClosuresCovered added (queue.taskSuccess occurrence result).2
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → queue.taskHasHealthyOwner node.task = true
            → let stored := queue.putTaskNode { node with value := some result.value }
              let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
              prepared.BufferedClosuresCovered added
                (queue.taskSuccess occurrence result).2)
        ∧ StreamReleasePublications work added (queue.taskSuccess occurrence result).2
        ∧ queue.StoredValuesConserved added (queue.taskSuccess occurrence result).1
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → queue.taskHasHealthyOwner node.task = true
            → ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1.StoredValuesConserved
                added (queue.taskSuccess occurrence result).1)
        ∧ BlocksFollowRegistrations (queue.taskSuccess occurrence result).1.tasks added
            (queue.taskSuccess occurrence result).2
        ∧ queue.StoredOwnersConserved added (queue.taskSuccess occurrence result).1
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → queue.taskHasHealthyOwner node.task = true
            → ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1.StoredOwnersConserved
                added (queue.taskSuccess occurrence result).1)
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → queue.taskHasHealthyOwner node.task = true
            → ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1.ReleaseOwners
                node.task.groups added)
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → queue.taskHasHealthyOwner node.task = true
            → ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1.ReleaseMembershipsCleared
                node.task.groups added) := by
  have current := inventory.mono (fun _ _ source =>
    source.mono (List.subset_append_left before [.taskSuccess occurrence result]))
  cases found : queue.taskNode? occurrence with
  | none =>
      refine ⟨
        [],
        by simp [State.taskSuccess, found],
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_
      ⟩
      · simpa only [State.taskSuccess, found, List.append_nil] using current
      · simpa only [State.taskSuccess, found] using State.BufferedClosuresCovered.nil queue
      · intro node impossible
        simp at impossible
      · simpa only [State.taskSuccess, found] using StreamReleasePublications.nil work
      · intro task buffered value lookup _ _
        exact Or.inr (by simpa only [State.taskSuccess, found] using lookup)
      · intro node impossible
        simp at impossible
      · simpa only [State.taskSuccess, found] using BlocksFollowRegistrations.nil queue.tasks []
      · simpa only [State.taskSuccess, found] using State.StoredOwnersConserved.refl queue
      · intro node impossible
        simp at impossible
      · intro node impossible
        simp at impossible
      · intro node impossible
        simp at impossible
  | some node =>
      cases healthy : queue.taskHasHealthyOwner node.task with
      | false =>
          refine ⟨
            [],
            by simp [State.taskSuccess, found, healthy],
            ?_,
            ?_,
            ?_,
            ?_,
            ?_,
            ?_,
            ?_,
            ?_,
            ?_,
            ?_,
            ?_
          ⟩
          · simpa only [State.taskSuccess, found, healthy, Bool.not_false, ↓reduceIte,
              List.append_nil] using State.PublicationInventory.mk
                current.unique current.provenance (current.stored.removeTask occurrence)
          · simpa only [State.taskSuccess, found, healthy, Bool.not_false, ↓reduceIte]
              using State.BufferedClosuresCovered.nil queue
          · intro other lookup guard
            have same := Option.some.inj lookup
            subst other
            simp [healthy] at guard
          · simpa only [State.taskSuccess, found, healthy, Bool.not_false, ↓reduceIte]
              using StreamReleasePublications.nil work
          · intro task buffered value lookup stored _
            have known := State.taskNode?_some lookup
            have source := (inventory.stored buffered known.1 value stored).1
            have different : task ≠ occurrence := by
              intro same
              exact fresh.2.2.1 occurrence List.mem_cons_self
                (same ▸ known.2 ▸ source.identity)
            exact Or.inr (by
              simpa only [State.taskSuccess, found, healthy, Bool.not_false, ↓reduceIte]
                using (queue.removeTask_lookup_other different).trans lookup)
          · intro other lookup guard
            have same := Option.some.inj lookup
            subst other
            simp [healthy] at guard
          · simpa only [State.taskSuccess, found, healthy, Bool.not_false, ↓reduceIte]
              using BlocksFollowRegistrations.nil (queue.removeTask occurrence).tasks []
          · intro task buffered value lookup stored key contributes present uncancelled
            have known := State.taskNode?_some lookup
            have source := (inventory.stored buffered known.1 value stored).1
            have different : task ≠ occurrence := by
              intro same
              exact fresh.2.2.1 occurrence List.mem_cons_self
                (same ▸ known.2 ▸ source.identity)
            refine Or.inr ⟨?_, ?_⟩
            · simpa only [State.taskSuccess, found, healthy, Bool.not_false, ↓reduceIte]
                using (queue.removeTask_lookup_other different).trans lookup
            · simpa only [State.taskSuccess, found, healthy, Bool.not_false, ↓reduceIte,
                State.removeTask, List.map_map, Function.comp_def] using present
          · intro other lookup guard
            have same := Option.some.inj lookup
            subst other
            simp [healthy] at guard
          · intro other lookup guard
            have same := Option.some.inj lookup
            subst other
            simp [healthy] at guard
          · intro other lookup guard
            have same := Option.some.inj lookup
            subst other
            simp [healthy] at guard
      | true =>
          obtain ⟨added, values, final, preparedCoverage, conservation, streams, ordered,
            owners, drainOwners, drainCleared⟩ :=
            current.taskSuccess_preparedCoverage generated accounted links settled children
              occurrence result matching node found healthy
              (fun member => fresh.2.2.1 occurrence List.mem_cons_self (included member))
              ⟨result, List.mem_append_right _ List.mem_cons_self, rfl⟩
              (inventory.fresh_success fresh) memberships
          have retained : ∀ task buffered value,
              queue.taskNode? task = some buffered → buffered.value = some value
              → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
                  result.work (some occurrence)).1.taskNode? task = some buffered := by
            intro task buffered value lookup stored
            have known := State.taskNode?_some lookup
            have source := (inventory.stored buffered known.1 value stored).1
            have different : occurrence ≠ task := by
              intro same
              exact fresh.2.2.1 occurrence List.mem_cons_self
                (same.symm ▸ known.2 ▸ source.identity)
            have retained := State.putTaskNode_lookup_other lookup
              { node with value := some result.value }
              ((State.taskNode?_some found).2 ▸ different)
            exact State.maybeIntegrateWork_lookup_other retained result.work
              (some occurrence) (fun same => different (Option.some.inj same))
          refine ⟨added, values, final, preparedCoverage.of_lookups retained, ?_, streams,
            State.StoredValuesConserved.of_lookups conservation retained,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro other lookup _
            have same := Option.some.inj lookup
            subst other
            exact preparedCoverage
          · intro other lookup _
            have same := Option.some.inj lookup
            subst other
            exact conservation
          · rw [State.taskSuccess_tasks found healthy]
            simpa only [State.maybeIntegrateWork_tasks_append, State.putTaskNode] using ordered
          · exact owners.of_lookups retained
              (State.maybeIntegrateWork_includesKeys
                (queue.putTaskNode { node with value := some result.value })
                result.work (some occurrence))
          · intro other lookup _
            have same := Option.some.inj lookup
            subst other
            exact owners
          · intro other lookup _
            have same := Option.some.inj lookup
            subst other
            exact drainOwners
          · intro other lookup _
            have same := Option.some.inj lookup
            subst other
            exact drainCleared

-----------------------------------------------------------------------------------------
-- Item integration retains every buffered lookup until the shared drain
-----------------------------------------------------------------------------------------

/-- An accepted item handler conserves entry buffers at every internal drain boundary.
`published` is that handler's single object ledger. The leading item event contains no
object values, so each bounded drain prefix uses its own object count without an offset.
-/
def State.StreamDrainOwners (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (published : List ObjectPublication)
    : Prop :=
  queue.rootStreams.contains stream.key = true
  → let prepared := queue.preparedStreamItems items
    ∀ steps,
      steps ≤ prepared.groupNodes.length
      → queue.StoredOwnersConserved
          (published.take
            ((State.drainReadyGroups.go steps prepared).2.flatMap
              WorkQueueEvent.objectValues).length)
          (State.drainReadyGroups.go steps prepared).1

/-- Every item-handler drain prefix excludes its earlier emitted object memberships.
`published` is the handler's one object ledger; its leading stream event adds no offset.
-/
def State.StreamDrainMembershipsCleared (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (published : List ObjectPublication)
    : Prop :=
  queue.rootStreams.contains stream.key = true
  → let prepared := queue.preparedStreamItems items
    ∀ steps,
      steps ≤ prepared.groupNodes.length
      → ∀ publication ∈
          published.take
            ((State.drainReadyGroups.go steps prepared).2.flatMap
              WorkQueueEvent.objectValues).length,
          (State.drainReadyGroups.go steps prepared).1.TaskMembershipAbsent publication.1

/-- Item arrival covers every earlier buffered contribution at any successful carrier.
Witness: integrate and activate all item children while retaining exact old task lookups
and the derived registry/link invariants; use the joint drain ledger after that fold.
The leading stream-values event contributes no object-publication offset.
-/
theorem State.PublicationInventory.streamItems_bufferedCoverage {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (generated : ExecutedWork work) (keys : queue.GroupKeysUnique)
    (live : queue.LiveGroupsRegistered) (registered : queue.TaskGroupsRegistered)
    (started : queue.StartedTasksRegistered) (links : queue.StoredTaskLinks)
    (settled : queue.ChildStreamsSettled) (children : queue.ChildStreamsMatchWork work)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (allCovered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
          ∃ group ∈ item.work.groups, group.node.key = key)
    (memberships : queue.GroupMembershipOrder)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.streamItems stream items).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.streamItems stream items).1.PublicationInventory property
            (published ++ added)
        ∧ queue.BufferedClosuresCovered added (queue.streamItems stream items).2
        ∧ StreamReleasePublications work added (queue.streamItems stream items).2
        ∧ queue.StoredValuesConserved added (queue.streamItems stream items).1
        ∧ BlocksFollowRegistrations (queue.streamItems stream items).1.tasks added
            (queue.streamItems stream items).2
        ∧ queue.StoredOwnersConserved added (queue.streamItems stream items).1
        ∧ queue.StreamDrainOwners stream items added
        ∧ queue.StreamDrainMembershipsCleared stream items added := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  let invariant (current : State) :=
    current.GroupKeysUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
    ∧ current.StartedTasksRegistered ∧ current.StoredTaskLinks
    ∧ current.ChildStreamsSettled ∧ current.ChildStreamsMatchWork work
    ∧ current.PublicationInventory property published
    ∧ (∀ occurrence node, queue.taskNode? occurrence = some node
      → current.taskNode? occurrence = some node)
    ∧ ∀ occurrence node value,
        queue.taskNode? occurrence = some node → node.value = some value
        → ∀ key ∈ node.task.groups.map Execution.DeliveryNode.key,
          key ∈ queue.groupNodes.map (fun owner => owner.group.node.key)
          → key ∈ current.groupNodes.map (fun owner => owner.group.node.key)
  have preserve (acc) (item : StreamItem) (member : item ∈ items)
      (prior : invariant acc.1) : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values⟩ := acc
    obtain ⟨unique, roots, covered, active, linked, ready, provenance, ledger, retained,
      owners⟩ := prior
    have integrated := current.maybeIntegrateWork_registration roots covered item.work
      (allCovered item member)
    have pruned := State.pruneEmptyGroups_registration integrated.1 integrated.2.1
      (current.maybeIntegrateWork item.work).2.newGroups
    have activated := State.startNewWork_registration pruned.1 pruned.2.1
      { (current.maybeIntegrateWork item.work).2 with
        newGroups := ((current.maybeIntegrateWork item.work).1.pruneEmptyGroups
          (current.maybeIntegrateWork item.work).2.newGroups).2 }
    have integratedLinks := linked.maybeIntegrateWork unique covered active item.work
    refine ⟨((unique.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _,
      activated.1, activated.2,
      ((active.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _,
      (integratedLinks.pruneEmptyGroups _).startNewWork _,
      ((ready.integrateRoots item.work).pruneEmptyGroups _).startNewWork _,
      ((provenance.integrateRoots item.work).pruneEmptyGroups _).startNewWork _,
      ⟨ledger.unique, ledger.provenance,
        ((ledger.stored.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _⟩,
      ?_, ?_⟩
    · intro occurrence node found
      apply State.startNewWork_lookup_existing
      change ((current.maybeIntegrateWork item.work).1.pruneEmptyGroups _).1.taskNodes.find? _ = _
      rw [State.pruneEmptyGroups_taskNodes]
      exact State.maybeIntegrateWork_lookup_other (retained occurrence node found) item.work
    · intro occurrence node value found stored key contributes present
      have integratedLookup := State.maybeIntegrateWork_lookup_other
        (retained occurrence node found) item.work
      have kept := State.pruneEmptyGroups_bufferedOwner_present integratedLinks
        (State.taskNode?_some integratedLookup).1 (by simp [stored]) contributes
        (current.maybeIntegrateWork_includesKeys item.work none key
          (owners occurrence node value found stored key contributes present))
        (current.maybeIntegrateWork item.work).2.newGroups
      rwa [(State.startNewWork_groupCore _ _).1]
  have loop (more : List StreamItem) (included : more.Subset items) (acc)
      (prior : invariant acc.1) : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (preserve acc item (included List.mem_cons_self) prior)
  obtain ⟨_, _, _, _, linked, ready, provenance, ledger, retained, owners⟩ :=
    loop items (fun _ member => member) (queue, [], [], [])
      ⟨keys, live, registered, started, links, settled, children, inventory,
        (fun _ _ found => found), fun _ _ _ _ _ _ _ present => present⟩
  have orderLoop (more : List StreamItem) (acc)
      (prior : acc.1.GroupMembershipOrder)
      : (more.foldl step acc).1.GroupMembershipOrder := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih _ (((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
  unfold State.streamItems
  split
  · rename_i inactive
    refine ⟨[], rfl, by simpa using inventory, .nil queue, .nil work,
      (fun _ _ _ found _ _ => Or.inr found), .nil _ _, .refl queue, ?_, ?_⟩
    all_goals
      intro active
      simp only [active, Bool.not_true, Bool.false_eq_true] at inactive
  · obtain ⟨added, values, final, covered, conserved, streams, ordered, prefixes, cleared⟩ :=
      ledger.drainReadyGroups_go_prefixCoverage linked
        (items.foldl step (queue, [], [], [])).1.groupNodes.length
    have coverage := covered.of_lookups (fun occurrence node _ found _ =>
      retained occurrence node found)
    have firstCoverage : queue.BufferedClosuresCovered []
        [.streamValues stream (items.foldl step (queue, [], [], [])).2.2.2
          (items.foldl step (queue, [], [], [])).2.1
          (items.foldl step (queue, [], [], [])).2.2.1] :=
      .of_noGroupSuccess (by intros; simp)
    have firstStreams : StreamReleasePublications work []
        [.streamValues stream (items.foldl step (queue, [], [], [])).2.2.2
          (items.foldl step (queue, [], [], [])).2.1
          (items.foldl step (queue, [], [], [])).2.2.1] :=
      .of_noGroupSuccess (by intros; simp)
    refine ⟨added, ?_, final, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [List.flatMap_cons, WorkQueueEvent.objectValues, List.nil_append,
        State.drainReadyGroups, step] using values
    · exact firstCoverage.append coverage rfl (fun _ _ _ found _ => Or.inr found)
    · exact firstStreams.append (streams work generated ready provenance) rfl
    · exact State.StoredValuesConserved.of_lookups conserved
        (fun occurrence node _ found _ => retained occurrence node found)
    · have blocks := ordered (orderLoop items (queue, [], [], []) memberships)
      rw [State.drainReadyGroups_tasks]
      exact blocks.control rfl
    · intro occurrence node value found stored key contributes present uncancelled
      have kept := prefixes _ (Nat.le_refl _) occurrence node value
        (retained occurrence node found) stored key contributes
        (owners occurrence node value found stored key contributes present) uncancelled
      exact kept.imp_left List.mem_of_mem_take
    · intro _
      dsimp only
      intro steps bounded occurrence node value found stored key contributes present uncancelled
      exact prefixes steps bounded occurrence node value (retained occurrence node found) stored key
        contributes (owners occurrence node value found stored key contributes present) uncancelled
    · intro _
      exact cleared

-----------------------------------------------------------------------------------------
-- One event-level certificate preserves the prepared-state evidence where it is needed
-----------------------------------------------------------------------------------------

/-- A successful input's prepared task map is covered at its handler's output carriers.
`published` labels that handler's object values. Other input kinds install no successful
object value and impose no prepared-state clause; their old values use buffered coverage.
-/
def State.PreparedClosuresCovered (queue : State) (event : GraphEvent)
    (published : List ObjectPublication)
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → queue.taskHasHealthyOwner node.task = true
        → let stored := queue.putTaskNode { node with value := some result.value }
          let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
          prepared.BufferedClosuresCovered published
            (queue.taskSuccess occurrence result).2
  | _ => True

/-- A successful input's prepared values are conserved through its remaining handler.
`published` labels that handler's object values. Other inputs have no prepared object map.
-/
def State.PreparedValuesConserved (queue : State) (event : GraphEvent)
    (published : List ObjectPublication)
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → queue.taskHasHealthyOwner node.task = true
        → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.StoredValuesConserved
            published (queue.taskSuccess occurrence result).1
  | _ => True

/-- A successful input retains its prepared buffered owners until publication or cancellation.
`published` is the same handler ledger used for values and closure coverage. Other source
events install no object value and therefore impose no prepared-state owner obligation.
-/
def State.PreparedOwnersConserved (queue : State) (event : GraphEvent)
    (published : List ObjectPublication)
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → queue.taskHasHealthyOwner node.task = true
        → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.StoredOwnersConserved
            published (queue.taskSuccess occurrence result).1
  | _ => True

/-- A value-producing input conserves buffered owners throughout owner processing and drain.
`published` fixes the whole handler's labels, including values flushed by the preceding
task-owner fold. Item handlers retain their entry buffers through preparation and each
drain prefix. Failure and stream-closure inputs do not emit object values.
-/
def State.PreparedReleaseOwners (queue : State) (event : GraphEvent)
    (published : List ObjectPublication)
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → queue.taskHasHealthyOwner node.task = true
        → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.ReleaseOwners
            node.task.groups published
  | .streamItems stream items => queue.StreamDrainOwners stream items published
  | _ => True

/-- A value-producing handler excludes earlier emitted memberships at release boundaries.
`published` is the same handler slice used for producer coverage and owner conservation.
Other source events emit no object values and have no successful release-drain phase.
-/
def State.PreparedMembershipsCleared (queue : State) (event : GraphEvent)
    (published : List ObjectPublication)
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → queue.taskHasHealthyOwner node.task = true
        → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.ReleaseMembershipsCleared
            node.task.groups published
  | .streamItems stream items =>
      queue.StreamDrainMembershipsCleared stream items published
  | _ => True

/-- Every fresh matching source event has one joint buffered/prepared/release ledger.
Witness: combine the task-success and item-arrival constructions; failures and stream
closures cannot carry successful group completions. All premises are internal replay
invariants or the existing source laws, not additional conformance assumptions.
-/
theorem State.PublicationInventory.handleGraphEvent_bufferedCoverage {queue : State}
    {work before published settledTasks}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work settledTasks)
    (included : settledTasks.Subset (before.flatMap (fun event => event.identities.1)))
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (event : GraphEvent)
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (memberships : queue.GroupMembershipOrder)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvent event).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvent event).1.PublicationInventory
            (ObjectValueFrom (before ++ [event])) (published ++ added)
        ∧ queue.BufferedClosuresCovered added (queue.handleGraphEvent event).2
        ∧ queue.PreparedClosuresCovered event added
        ∧ StreamReleasePublications work added (queue.handleGraphEvent event).2
        ∧ queue.StoredValuesConserved added (queue.handleGraphEvent event).1
        ∧ queue.PreparedValuesConserved event added
        ∧ BlocksFollowRegistrations (queue.handleGraphEvent event).1.tasks added
            (queue.handleGraphEvent event).2
        ∧ queue.StoredOwnersConserved added (queue.handleGraphEvent event).1
        ∧ queue.PreparedOwnersConserved event added
        ∧ queue.PreparedReleaseOwners event added
        ∧ queue.PreparedMembershipsCleared event added := by
  have current := inventory.mono (fun _ _ source =>
    source.mono (List.subset_append_left before [event]))
  cases event with
  | taskSuccess occurrence result =>
      exact inventory.taskSuccess_bufferedCoverage generated accounted included links settled
        children occurrence result matching fresh memberships
  | taskFailure occurrence errors =>
      obtain ⟨added, values, final, streams⟩ := current.handleGraphEvent_streamRelease
        settled children generated (.taskFailure occurrence errors) matching
        (by intro task result impossible; cases impossible)
      refine ⟨
        added,
        values,
        final,
        .of_noGroupSuccess (queue.taskFailure_noGroupSuccess occurrence errors),
        trivial,
        streams,
        ?_,
        trivial,
        BlocksFollowRegistrations.of_noObjectValues _ _
          (queue.taskFailure_objectValues occurrence errors),
        (inventory.taskFailure_storedOwnersConserved occurrence errors fresh).of_empty
          added,
        trivial,
        trivial,
        trivial
      ⟩
      intro task node value found stored survivor
      have known := State.taskNode?_some found
      have source := (inventory.stored node known.1 value stored).1
      have different : task ≠ occurrence := by
        intro same
        exact fresh.2.2.1 occurrence List.mem_cons_self
          (same ▸ known.2 ▸ source.identity)
      obtain ⟨contributor, contributes, owner, live⟩ := survivor
      exact Or.inr
        (State.taskFailure_lookup_survivingOwner found occurrence errors different
          contributes (List.mem_of_find?_eq_some live) (State.groupNode?_key live))
  | streamItems stream items =>
      obtain ⟨added, values, final, covered, streams, conserved,
        ordered, owners, prefixes, cleared⟩ :=
        current.streamItems_bufferedCoverage
        generated accounted.keys accounted.liveGroups accounted.taskGroups accounted.started
        links settled children stream items
        (fun _ member => matching.streamItem_childTasksCovered member) memberships
      exact ⟨added, values, final, covered, trivial, streams, conserved, trivial, ordered,
        owners, trivial, prefixes, cleared⟩
  | streamSuccess stream =>
      obtain ⟨added, values, final, streams⟩ := current.handleGraphEvent_streamRelease
        settled children generated (.streamSuccess stream) matching
        (by intro task result impossible; cases impossible)
      have owners : queue.StoredOwnersConserved added (queue.streamSuccess stream).1 := by
        intro occurrence node value found stored key contributes present uncancelled
        unfold State.streamSuccess
        split <;> exact Or.inr ⟨found, present⟩
      refine ⟨
        added,
        values,
        final,
        .of_noGroupSuccess ?_,
        trivial,
        streams,
        ?_,
        trivial,
        BlocksFollowRegistrations.of_noObjectValues _ _ ?_,
        owners,
        trivial,
        trivial,
        trivial
      ⟩
      · intro group groups streams
        simp only [State.handleGraphEvent, State.streamSuccess]
        split <;> simp
      · intro task node value found _ _
        apply Or.inr
        change (queue.streamSuccess stream).1.taskNode? task = some node
        unfold State.streamSuccess
        split <;> exact found
      · simp only [State.handleGraphEvent, State.streamSuccess]
        split <;> rfl
  | streamFailure stream errors =>
      obtain ⟨added, values, final, streams⟩ := current.handleGraphEvent_streamRelease
        settled children generated (.streamFailure stream errors) matching
        (by intro task result impossible; cases impossible)
      have owners : queue.StoredOwnersConserved added (queue.streamFailure stream errors).1 := by
        intro occurrence node value found stored key contributes present uncancelled
        unfold State.streamFailure
        split <;> exact Or.inr ⟨found, present⟩
      refine ⟨
        added,
        values,
        final,
        .of_noGroupSuccess ?_,
        trivial,
        streams,
        ?_,
        trivial,
        BlocksFollowRegistrations.of_noObjectValues _ _ ?_,
        owners,
        trivial,
        trivial,
        trivial
      ⟩
      · intro group groups streams
        simp only [State.handleGraphEvent, State.streamFailure]
        split <;> simp
      · intro task node value found _ _
        apply Or.inr
        change (queue.streamFailure stream errors).1.taskNode? task = some node
        unfold State.streamFailure
        split <;> exact found
      · simp only [State.handleGraphEvent, State.streamFailure]
        split <;> rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
