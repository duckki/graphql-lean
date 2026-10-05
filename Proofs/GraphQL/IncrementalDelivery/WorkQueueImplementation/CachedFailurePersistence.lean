import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancelledGroupReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! A retained failure cannot silently disappear during successful bookkeeping. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A fixed failed ref remains cached or is permanently marked as cancelled
-----------------------------------------------------------------------------------------

/-- The concrete queue retains a failure at `ref`, either as a live cache or a permanent
cancellation marker. This proof-only state predicate does not assume a wire report.
-/
def State.FailureRetained (queue : State) (ref : NodeRef) : Prop :=
  ref ∈ queue.cancelledGroups
  ∨ ∃ node ∈ queue.groupNodes, node.group.node.ref = ref ∧ node.failure.isSome = true

/-- Equal group nodes and cancellation markers retain the same fixed failure.
Witness: transport either concrete state witness unchanged.
-/
theorem State.FailureRetained.of_same {before after : State} {ref}
    (retained : before.FailureRetained ref)
    (nodes : after.groupNodes = before.groupNodes)
    (markers : before.cancelledGroups.Subset after.cancelledGroups)
    : after.FailureRetained ref := by
  rcases retained with cancelled | ⟨node, member, same, cached⟩
  · exact .inl (markers cancelled)
  · exact .inr ⟨node, nodes.symm ▸ member, same, cached⟩

/-- A group update retains a fixed failure if it does not clear any replaced cache.
Witness: map the old cache witness or retain the existing cancellation marker.
-/
theorem State.FailureRetained.putGroupNode {queue : State} {ref}
    (retained : queue.FailureRetained ref) (updated : GroupNode)
    (preserved
      : ∀ old ∈ queue.groupNodes,
          old.group.node.ref = updated.group.node.ref
          → old.failure.isSome = true
          → updated.failure.isSome = true)
    : (queue.putGroupNode updated).FailureRetained ref := by
  rcases retained with cancelled | ⟨node, member, same, cached⟩
  · exact .inl cancelled
  · by_cases equal : node.group.node.ref = updated.group.node.ref
    · exact .inr ⟨updated, List.mem_map.mpr ⟨node, member, by simp [equal]⟩,
        equal.symm.trans same, preserved node member equal cached⟩
    · exact .inr ⟨node, List.mem_map.mpr ⟨node, member, by simp [equal]⟩, same, cached⟩

/-- Updating a looked-up node's counters without clearing its cache retains failures.
Witness: unique refs identify every replaced record with the looked-up record.
-/
theorem State.FailureRetained.putCounters {queue : State} {ref target node}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (found : queue.groupNode? target = some node) (pending : Nat) (failure : Option Nat)
    (preserved : node.failure.isSome = true → failure.isSome = true)
    : (queue.putGroupNode { node with pending, failure }).FailureRetained ref := by
  apply retained.putGroupNode
  intro old member same cached
  have equal := unique.sameNode member (List.mem_of_find?_eq_some found) same
  subst old
  exact preserved cached

/-- Fresh group registration retains every earlier cache or cancellation marker.
Witness: repeated/refused registration leaves nodes alone; fresh registration appends.
-/
theorem State.FailureRetained.addGroup {queue : State} {ref}
    (retained : queue.FailureRetained ref) (group : Group)
    : (queue.addGroup group).FailureRetained ref := by
  unfold State.addGroup
  split
  · exact retained
  · split
    · exact retained.of_same rfl (List.subset_append_left _ _)
    · rcases retained with cancelled | ⟨node, member, same, cached⟩
      · exact .inl cancelled
      · exact .inr ⟨node, List.mem_append_left _ member, same, cached⟩

/-- Parent linking retains every earlier failure cache.
Witness: group registration retains caches; unique refs justify replacing child links
without changing the selected parent's cache.
-/
theorem State.FailureRetained.addGroups {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (groups : List Group)
    : (queue.addGroups groups).1.FailureRetained ref := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  let link (current : State) (group : Group) :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.ref then
              node.childGroups else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have register (more : List Group) (current : State)
      (prior : current.FailureRetained ref) (refs : current.GroupRefsUnique)
      : (more.foldl State.addGroup current).FailureRetained ref
        ∧ (more.foldl State.addGroup current).GroupRefsUnique := by
    induction more generalizing current with
    | nil => exact ⟨prior, refs⟩
    | cons group rest ih => exact ih _ (prior.addGroup group) (refs.addGroup group)
  have linked (more : List Group) (current : State)
      (prior : current.FailureRetained ref) (refs : current.GroupRefsUnique)
      : (more.foldl link current).FailureRetained ref := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        · unfold link
          split
          · exact prior
          · split
            · exact prior
            · rename_i node found
              apply prior.putGroupNode
              intro old member same cached
              have equal := refs.sameNode member (List.mem_of_find?_eq_some found) same
              subst old
              exact cached
        · unfold link
          split
          · exact refs
          · split
            · exact refs
            · exact refs.putGroupNode _
  obtain ⟨reported, refs⟩ := register fresh queue retained unique
  exact linked fresh _ reported refs

/-- Task installation retains all existing caches.
Witness: each contributor update changes only pending counts and task membership.
-/
theorem State.FailureRetained.addTask {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique) (task : Task)
    : (queue.addTask task).FailureRetained ref := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have fold (more : List Execution.DeliveryNode) (current : State)
      (prior : current.FailureRetained ref) (refs : current.GroupRefsUnique)
      : (more.foldl step current).FailureRetained ref := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        · unfold step
          split
          · exact prior
          · rename_i node found
            split
            · exact prior
            · apply prior.putGroupNode
              intro old member same cached
              have equal := refs.sameNode member (List.mem_of_find?_eq_some found) same
              subst old
              exact cached
        · unfold step
          split
          · exact refs
          · split
            · exact refs
            · exact refs.putGroupNode _
  dsimp only [State.addTask]
  split <;> exact fold task.groups { queue with tasks := queue.tasks ++ [task] } retained unique

/-- Stream installation leaves group caches and cancellation markers unchanged.
Witness: all root-stream and task-linked stream branches change only stream/task data.
-/
theorem State.FailureRetained.addStreams {queue : State} {ref}
    (retained : queue.FailureRetained ref) (streams : List Stream)
    (producer : Option Occurrence := none)
    : (queue.addStreams streams producer).1.FailureRetained ref := by
  dsimp only [State.addStreams]
  split
  · exact retained
  · split <;> exact retained

/-- Work integration cannot forget an earlier retained failure.
Witness: thread cache retention and unique refs through groups, tasks, and streams.
-/
theorem State.FailureRetained.maybeIntegrateWork {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (work : Work) (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork work producer).1.FailureRetained ref := by
  have fold (tasks : List Task) (current : State) (prior : current.FailureRetained ref)
      (refs : current.GroupRefsUnique)
      : (tasks.foldl State.addTask current).FailureRetained ref := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.addTask refs task) (refs.addTask task)
  exact (fold work.tasks _ (retained.addGroups unique work.groups)
    (unique.addGroups work.groups)).addStreams work.streams producer

-----------------------------------------------------------------------------------------
-- Pruning and successful closure may remove only cache-free records
-----------------------------------------------------------------------------------------

/-- Task retirement does not clear any group cache or cancellation marker.
Witness: its group map changes only task memberships.
-/
theorem State.FailureRetained.removeTask {queue : State} {ref}
    (retained : queue.FailureRetained ref) (task : Occurrence)
    : (queue.removeTask task).FailureRetained ref := by
  rcases retained with cancelled | ⟨node, member, same, cached⟩
  · exact .inl cancelled
  · exact .inr ⟨{ node with tasks := node.tasks.filter (· != task) },
      List.mem_map_of_mem member, same, cached⟩

/-- Failure cleanup cannot silently erase a retained cache.
Witness: every filtered-out ref is appended to the permanent cancellation registry.
-/
theorem State.FailureRetained.removeGroup {queue : State} {ref}
    (retained : queue.FailureRetained ref) (root : NodeRef)
    : (queue.removeGroup root).FailureRetained ref := by
  rcases retained with cancelled | ⟨node, member, same, cached⟩
  · exact .inl (List.mem_append_left _ cancelled)
  · by_cases removed : ref ∈ State.removeGroup.collect (queue.groupNodes.length + 1)
        queue [root] []
    · exact .inl (List.mem_append_right _ removed)
    · exact .inr ⟨node, List.mem_filter.mpr ⟨member, by simp [same, removed]⟩, same, cached⟩

/-- Empty-shell pruning never discards a retained failure cache.
Witness: a removed record must have no cache; unique refs exclude the fixed cached
record from each such filter. Activation is irrelevant to this state-only fact.
-/
theorem State.FailureRetained.pruneEmptyGroups {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.FailureRetained ref := by
  have loop (fuel : Nat) (current : State) (remaining kept)
      (prior : current.FailureRetained ref) (refs : current.GroupRefsUnique)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.FailureRetained ref := by
    induction fuel generalizing current remaining kept with
    | zero => exact prior
    | succ fuel ih =>
        cases remaining with
        | nil => exact prior
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ prior refs
            · rename_i node found
              split
              · rename_i empty
                have parts : node.tasks.isEmpty = true ∧ node.failure.isNone = true := by
                  simpa only [Bool.and_eq_true] using empty
                have noCache : node.failure = none := by simpa using parts.2
                apply ih
                · rcases prior with cancelled | ⟨cached, member, same, failed⟩
                  · exact .inl cancelled
                  · have different : cached.group.node.ref ≠ group.ref := by
                      intro equal
                      have identical := refs.sameNode member (List.mem_of_find?_eq_some found)
                        (equal.trans (State.groupNode?_ref found).symm)
                      subst cached
                      simp [noCache] at failed
                    exact .inr ⟨cached, List.mem_filter.mpr ⟨member, by simp [different]⟩,
                      same, failed⟩
                · exact State.GroupRefsUnique.filterGroupNodes refs _
              · exact ih _ _ _ prior refs
  exact loop _ queue groups [] retained unique

/-- Starting released work leaves every cache and cancellation marker intact.
Witness: the exact group-map and cancellation-registry equations for activation.
-/
theorem State.FailureRetained.startNewWork {queue : State} {ref}
    (retained : queue.FailureRetained ref) (released : NewWork)
    : (queue.startNewWork released).FailureRetained ref :=
  retained.of_same (queue.startNewWork_groupCore released).1
    (by rw [State.startNewWork_cancelledGroups]; exact List.Subset.refl _)

/-- Successful closure cannot remove a cached group as though it had succeeded.
Witness: the selected live group's cache is empty. Unique refs exclude the fixed failure
from its own-ref filter; task retirement and subsequent pruning retain other caches.
-/
theorem State.FailureRetained.finishGroupSuccess {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (group : GroupNode) (member : group ∈ queue.groupNodes) (clear : group.failure = none)
    : (queue.finishGroupSuccess group).1.FailureRetained ref := by
  have different : ref ≠ group.group.node.ref ∨ ref ∈ queue.cancelledGroups := by
    rcases retained with cancelled | ⟨node, included, same, cached⟩
    · exact .inr cancelled
    · apply Or.inl
      intro equal
      have identical := unique.sameNode included member (same.trans equal)
      subst node
      simp [clear] at cached
  let step (acc : State × List Execution.ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some node =>
        let values := match node.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ node.childStreams)
  have fold (tasks : List Occurrence)
      (acc : State × List Execution.ExecutionGroupValue × NodeRefs)
      (prior : acc.1.FailureRetained ref) (refs : acc.1.GroupRefsUnique)
      : (tasks.foldl step acc).1.FailureRetained ref
        ∧ (tasks.foldl step acc).1.GroupRefsUnique := by
    induction tasks generalizing acc with
    | nil => exact ⟨prior, refs⟩
    | cons task rest ih =>
        apply ih
        · dsimp only [step]
          split
          · exact prior
          · exact prior.removeTask _
        · dsimp only [step]
          split
          · exact refs
          · exact refs.removeTask _
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  obtain ⟨prior, refs⟩ := fold group.tasks (queue, [], []) retained unique
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.FailureRetained ref := by
    rcases prior with cancelled | ⟨node, included, same, cached⟩
    · exact .inl cancelled
    · rcases different with unequal | cancelled
      · exact .inr ⟨node, List.mem_filter.mpr ⟨included, by simp [same, unequal]⟩,
          same, cached⟩
      · have stable : flushed.cancelledGroups = queue.cancelledGroups := by
          have loop (tasks : List Occurrence)
              (acc : State × List Execution.ExecutionGroupValue × NodeRefs)
              : (tasks.foldl step acc).1.cancelledGroups = acc.1.cancelledGroups := by
            induction tasks generalizing acc with
            | nil => rfl
            | cons task rest ih =>
                rw [List.foldl_cons, ih]
                dsimp only [step]
                split <;> rfl
          exact loop group.tasks (queue, [], [])
        exact .inl (stable.symm ▸ cancelled)
  exact filtered.pruneEmptyGroups (State.GroupRefsUnique.filterGroupNodes refs _) _

/-- Recursive release retains a cached failure or records its cancellation ref.
Witness: successful branches require an empty cache; failed branches remove their
subtree with permanent markers. This property is independent of emitted output.
-/
theorem State.FailureRetained.drainReadyGroups {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    : queue.drainReadyGroups.1.FailureRetained ref := by
  have preserved := State.drainReadyGroups_preserves
    (fun current => current.FailureRetained ref ∧ current.GroupRefsUnique)
    (fun current node prior member _ clear _ =>
      ⟨(prior.1.finishGroupSuccess prior.2 node member clear).startNewWork _,
        (prior.2.finishGroupSuccess node).startNewWork _⟩)
    (fun current node errors prior _ _ _ =>
      ⟨prior.1.removeGroup _, prior.2.removeGroup _⟩)
    (valid := And.intro retained unique)
  exact preserved.1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
