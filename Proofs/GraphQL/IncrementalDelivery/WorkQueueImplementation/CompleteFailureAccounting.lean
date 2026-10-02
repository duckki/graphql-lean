import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrorAccumulation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage

/-! Complete error accounting for live caches and not-yet-registered group keys. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- NodeErrors counts the chosen failure inventory, including nonowner zero contributions
-----------------------------------------------------------------------------------------

/-- Prepending a known task adds its exact contribution, whether or not it owns the key.
Witness: extend the old contribution function at that task. Descriptor uniqueness makes
the extension agree on earlier occurrences too, so no freshness or positivity is required.
-/
theorem nodeErrors_cons {work failed key errors occurrence owners producer payload}
    (counts : NodeErrors work failed key errors)
    (known : TaskAt work occurrence owners producer payload)
    : NodeErrors work (occurrence :: failed) key
        ((if key ∈ owners then payload.failure.getD 0 else 0) + errors) := by
  classical
  obtain ⟨contribution, assigned, total⟩ := counts
  let count := if key ∈ owners then payload.failure.getD 0 else 0
  let extended := fun other => if other = occurrence then count else contribution other
  have same : ∀ other ∈ failed, extended other = contribution other := by
    intro other member
    by_cases equal : other = occurrence
    · subst other
      obtain ⟨oldOwners, parent, value, descriptor, counted⟩ := assigned occurrence member
      obtain ⟨rfl, _, rfl⟩ := known.unique descriptor
      simpa [extended, count] using counted.symm
    · simp [extended, equal]
  refine ⟨extended, ?_, ?_⟩
  · intro other member
    rcases List.mem_cons.mp member with equal | earlier
    · subst other
      exact ⟨owners, producer, payload, known, by simp [extended, count]⟩
    · obtain ⟨oldOwners, parent, value, descriptor, counted⟩ := assigned other earlier
      exact ⟨oldOwners, parent, value, descriptor, (same other earlier).trans counted⟩
  · rw [List.map_cons, List.sum_cons, List.map_congr_left same]
    simpa [extended, count] using congrArg (count + ·) total

/-- The empty failure inventory contributes zero to every key.
Witness: the constant-zero contribution function and empty sum.
-/
theorem nodeErrors_nil (work : Execution.Work) (key : Nat) : NodeErrors work [] key 0 :=
  ⟨fun _ => 0, by simp, rfl⟩

-----------------------------------------------------------------------------------------
-- Full inventory accounting includes empty caches and future fresh registrations
-----------------------------------------------------------------------------------------

/-- Every live cache counts all `failed` tasks; an unregistered key counts zero.
Replay instantiates this proof-only inventory with eligible object failures, excluding
ignored settlements. Fresh-key accounting lets later integration retain prior totals.
-/
def State.GroupErrorAccounting (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  (∀ node ∈ queue.groupNodes,
    NodeErrors work failed node.group.node.key (node.failure.getD 0))
  ∧ ∀ key, key ∉ queue.registeredGroups → NodeErrors work failed key 0

/-- Complete accounting supplies every live cache's exact full-inventory total.
Witness: project the live-node clause.
-/
theorem State.GroupErrorAccounting.live {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed)
    : ∀ node ∈ queue.groupNodes,
        NodeErrors work failed node.group.node.key (node.failure.getD 0) :=
  counts.1

/-- Complete accounting supplies zero contribution at every unregistered key.
Witness: project the fresh-key clause, including failure descriptors for the full inventory.
-/
theorem State.GroupErrorAccounting.fresh {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed)
    : ∀ key, key ∉ queue.registeredGroups → NodeErrors work failed key 0 :=
  counts.2

/-- Replacing a group preserves complete accounting when its cache has the exact count.
Witness: each mapped node is old or the certified replacement; registrations do not change.
-/
theorem State.GroupErrorAccounting.putGroupNode {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (updated : GroupNode)
    (exactCount : NodeErrors work failed updated.group.node.key (updated.failure.getD 0))
    : (queue.putGroupNode updated).GroupErrorAccounting work failed := by
  refine ⟨?_, counts.fresh⟩
  intro node member
  dsimp only [State.putGroupNode] at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact exactCount
  · subst node; exact counts.live old oldMember

/-- Fresh registration has zero earlier error contribution, not merely an empty cache.
Witness: permanent-registration freshness discharges the full inventory's zero count.
-/
theorem State.GroupErrorAccounting.addGroup {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (group : Group)
    : (queue.addGroup group).GroupErrorAccounting work failed := by
  unfold State.addGroup
  split
  · exact counts
  · rename_i fresh
    have unregistered : group.node.key ∉ queue.registeredGroups := by
      simp only [Bool.or_eq_true, List.contains_iff_mem, not_or] at fresh
      exact fresh.1
    dsimp only
    split
    · exact ⟨counts.live, fun key absent =>
        counts.fresh key (fun member => absent (List.mem_append_left _ member))⟩
    · refine ⟨?_, ?_⟩
      · intro node member
        rcases List.mem_append.mp member with old | added
        · exact counts.live node old
        · cases List.mem_singleton.mp added
          exact counts.fresh group.node.key unregistered
      · intro key absent
        exact counts.fresh key (fun member => absent (List.mem_append_left _ member))

/-- Task removal changes memberships but neither error counts nor registration history.
Witness: the group map retains each node's key and exact cache.
-/
theorem State.GroupErrorAccounting.removeTask {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupErrorAccounting work failed := by
  refine ⟨?_, counts.fresh⟩
  intro node member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact counts.live old oldMember

/-- Cancellation preserves the exact totals of surviving groups and future fresh keys.
Witness: live nodes are only filtered and the permanent registry remains unchanged.
-/
theorem State.GroupErrorAccounting.removeGroup {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (key : Nat)
    : (queue.removeGroup key).GroupErrorAccounting work failed :=
  ⟨fun node member => counts.live node (List.mem_filter.mp member).1, counts.fresh⟩

/-- An eligible failure adds its contribution to every surviving owning cache.
Witness: the once-per-owner recurrence and NodeErrors extension over the entire inventory.
Ignored settlements retain the old ledger and caches; registered ownership keeps every
still-fresh key's count at zero in the eligible branch.
-/
theorem State.GroupErrorAccounting.taskFailure {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (generated : ExecutedWork work)
    (live : queue.LiveGroupsRegistered) (covered : queue.TaskGroupsRegistered)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence) (errors : Nat)
    (task : TaskNode) (found : queue.taskNode? occurrence = some task)
    (source : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : (queue.taskFailure occurrence errors).1.GroupErrorAccounting work
        (queue.objectFailureContribution (.taskFailure occurrence errors) ++ failed) := by
  cases eligible : queue.taskHasHealthyOwner task.task with
  | false =>
      simpa only [State.taskFailure, found, eligible, Bool.not_false, ↓reduceIte,
        State.objectFailureContribution, Bool.false_eq_true, List.nil_append]
        using counts.removeTask occurrence
  | true =>
      simp only [State.objectFailureContribution, found, eligible, ↓reduceIte,
        List.singleton_append]
      have registeredTask := registered task (List.mem_of_find?_eq_some found)
      have distinct := matching.contributorsNodup generated registeredTask
      have atTask := (State.taskNode?_some found).2
      obtain ⟨⟨_, _, _, _, descriptor⟩, _⟩ := matching task.task registeredTask
      rw [atTask] at descriptor
      obtain ⟨owners, producer, path, known⟩ := source
      have sameOwners := (descriptor.unique known).1
      refine ⟨?_, ?_⟩
      · intro node member
        obtain ⟨old, oldMember, sameKey, updated⟩ := queue.taskFailure_cachedErrors
          occurrence errors task found distinct member
        have next := nodeErrors_cons (counts.live old oldMember) known
        rw [sameKey] at next
        rw [updated]
        simp only [eligible, true_and]
        by_cases owner : node.group.node.key ∈ task.task.groups.map Execution.DeliveryNode.key
        · have owns : node.group.node.key ∈ owners := sameOwners ▸ owner
          simpa [owner, owns, Payload.failure, Nat.add_comm] using next
        · have absent : node.group.node.key ∉ owners := sameOwners ▸ owner
          simpa [owner, absent] using next
      · intro key absent
        rw [(queue.taskFailure_registration live covered occurrence errors).2.2] at absent
        have nonowner : key ∉ owners := by
          intro owner
          exact absent (covered task.task registeredTask key (sameOwners.symm ▸ owner))
        simpa [nonowner] using nodeErrors_cons (counts.fresh key absent) known

-----------------------------------------------------------------------------------------
-- Integration cannot forget a contribution recorded before a key was registered
-----------------------------------------------------------------------------------------

/-- A state invariant survives a fold of preserving operations.
Witness: induction over the actual fold, retaining each intermediate state.
-/
private theorem fold_preserves {α β : Type} (property : β → Prop)
    (step : β → α → β) (items : List α)
    (preserved : ∀ state item, property state → property (step state item))
    (state : β) (valid : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact valid
  | cons item rest ih => exact ih _ (preserved state item valid)

/-- Group integration preserves complete totals through registration and parent linking.
Witness: fresh registrations count zero; link installation changes neither keys nor caches.
-/
theorem State.GroupErrorAccounting.addGroups {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (groups : List Group)
    : (queue.addGroups groups).1.GroupErrorAccounting work failed := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  let link (current : State) (group : Group) :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.key then
              node.childGroups else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have linked (current : State) (group : Group)
      (valid : current.GroupErrorAccounting work failed)
      : (link current group).GroupErrorAccounting work failed := by
    unfold link
    split
    · exact valid
    · split
      · exact valid
      · rename_i node found
        exact valid.putGroupNode _ (valid.live node (List.mem_of_find?_eq_some found))
  change (fresh.foldl link (fresh.foldl State.addGroup queue)).GroupErrorAccounting work failed
  exact fold_preserves _ link fresh linked _
    (fold_preserves (fun current : State => current.GroupErrorAccounting work failed)
      State.addGroup fresh (fun _ group valid => valid.addGroup group) queue counts)

/-- Task registration adds memberships without changing complete error totals.
Witness: each contributor update preserves its key/cache and the permanent registry.
-/
theorem State.GroupErrorAccounting.addTask {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (task : Task)
    : (queue.addTask task).GroupErrorAccounting work failed := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stable (current : State) (group : Execution.DeliveryNode)
      (valid : current.GroupErrorAccounting work failed)
      : (step current group).GroupErrorAccounting work failed := by
    unfold step
    split
    · exact valid
    · rename_i node found
      split
      · exact valid
      · exact valid.putGroupNode _ (valid.live node (List.mem_of_find?_eq_some found))
  have folded := fold_preserves _ step task.groups stable registered counts
  dsimp only [State.addTask]
  split <;> exact folded

/-- Stream registration leaves complete group error accounting unchanged.
Witness: only stream and producer-task records are updated.
-/
theorem State.GroupErrorAccounting.addStreams {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.GroupErrorAccounting work failed := by
  dsimp only [State.addStreams]
  split
  · exact counts
  · split <;> exact counts

/-- Integrating arbitrary child work preserves every full-inventory group total.
Witness: group, task, and stream registration, including fresh-key zero accounting.
No availability or already-admitted-output assumption is required for error arithmetic.
-/
theorem State.GroupErrorAccounting.maybeIntegrateWork {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (more : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork more producer).1.GroupErrorAccounting work failed :=
  (fold_preserves (fun current : State => current.GroupErrorAccounting work failed)
    State.addTask more.tasks (fun _ task valid => valid.addTask task) _
    (counts.addGroups more.groups)).addStreams
    more.streams producer

-----------------------------------------------------------------------------------------
-- Release and drain retain exact totals on every surviving group
-----------------------------------------------------------------------------------------

/-- Pruning only filters live nodes and preserves the fresh-key zero-count certificate.
Witness: induction over the pruning budget with the complete invariant.
-/
theorem State.GroupErrorAccounting.pruneEmptyGroups {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupErrorAccounting work failed := by
  have loop (fuel : Nat) (current : State) (remaining kept)
      (valid : current.GroupErrorAccounting work failed)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupErrorAccounting
          work failed := by
    induction fuel generalizing current remaining kept with
    | zero => exact valid
    | succ fuel ih =>
        cases remaining with
        | nil => exact valid
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ valid
            · split
              · exact ih _ _ _
                  ⟨fun node member => valid.live node (List.mem_filter.mp member).1, valid.fresh⟩
              · exact ih _ _ _ valid
  exact loop _ queue groups [] counts

/-- Activation preserves all live cache totals and zero totals for unregistered keys.
Witness: group/task/stream starts change no error cache or permanent group registration.
-/
theorem State.GroupErrorAccounting.startNewWork {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (more : NewWork)
    : (queue.startNewWork more).GroupErrorAccounting work failed := by
  have taskStable (current : State) (occurrence : Occurrence)
      (valid : current.GroupErrorAccounting work failed)
      : (current.startTask occurrence).GroupErrorAccounting work failed := by
    unfold State.startTask
    split
    · exact valid
    · split <;> exact valid
  have groupStable (current : State) (key : Nat)
      (valid : current.GroupErrorAccounting work failed)
      : (current.startGroup key).GroupErrorAccounting work failed := by
    unfold State.startGroup
    split
    · exact valid
    · rename_i node found
      split
      · exact valid
      · exact fold_preserves _ State.startTask node.tasks taskStable current valid
  have streamStable (current : State) (key : Nat)
      (valid : current.GroupErrorAccounting work failed)
      : (current.startStream key).GroupErrorAccounting work failed := by
    unfold State.startStream
    split <;> exact valid
  exact fold_preserves _ State.startStream _ streamStable _
    (fold_preserves _ State.startGroup _ groupStable _ counts)

/-- A successful flush retains complete totals on all surviving groups.
Witness: task retirement, closing-key filtering, and descendant pruning preserve the
full-inventory invariant, even when other groups have cached failures.
-/
theorem State.GroupErrorAccounting.finishGroupSuccess {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupErrorAccounting work failed := by
  let step (acc : State × List ExecutionGroupValue × Keys) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some node =>
        let values := match node.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ node.childStreams)
  have stable (acc : State × List ExecutionGroupValue × Keys) (occurrence : Occurrence)
      (valid : acc.1.GroupErrorAccounting work failed)
      : (step acc occurrence).1.GroupErrorAccounting work failed := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact valid
    · exact valid.removeTask occurrence
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have prior : flushed.GroupErrorAccounting work failed :=
    fold_preserves _ step group.tasks stable (queue, [], []) counts
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.key != group.group.node.key)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have filtered : current.GroupErrorAccounting work failed :=
    ⟨fun node member => prior.live node (List.mem_filter.mp member).1, prior.fresh⟩
  exact filtered.pruneEmptyGroups _

/-- Recursive release preserves the complete inventory's error totals.
Witness: the actual drain alternates successful flush/activation and failure removal.
-/
theorem State.GroupErrorAccounting.drainReadyGroups {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed)
    : queue.drainReadyGroups.1.GroupErrorAccounting work failed := by
  apply State.drainReadyGroups_preserves
    (fun current => current.GroupErrorAccounting work failed) (valid := counts)
  · intro current node valid _ _ _ _
    exact (valid.finishGroupSuccess node).startNewWork _
  · intro current node errors valid _ _ _
    exact valid.removeGroup node.group.node.key

/-- Initial work integration establishes complete zero-error accounting.
Witness: the empty source inventory counts zero at every key, through integration and start.
-/
theorem createWorkQueue_groupErrorAccounting (input : Work) (work : Execution.Work)
    : (State.initialize input).GroupErrorAccounting work [] := by
  have empty : ({} : State).GroupErrorAccounting work [] :=
    ⟨(by intro node member; cases member), fun key _ => nodeErrors_nil work key⟩
  exact ((empty.maybeIntegrateWork input).pruneEmptyGroups _).startNewWork _

-----------------------------------------------------------------------------------------
-- Successful inputs can release caches but cannot lose their counted contributions
-----------------------------------------------------------------------------------------

/-- Successful settlement preserves full-inventory totals through integration and release.
Witness: every contributor decrement/flush preserves caches, followed by the actual drain.
-/
theorem State.GroupErrorAccounting.taskSuccess {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.GroupErrorAccounting work failed := by
  let step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode) :=
    let (current, outputs, released) := acc
    match current.groupNode? group.key with
    | none => (current, outputs, released)
    | some old =>
        let node := { old with pending := old.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.key && node.pending == 0 && node.failure.isNone then
          let (next, finished, more) := current.finishGroupSuccess node
          (next, outputs ++ finished,
            ⟨released.newGroups ++ more.newGroups, released.newStreams ++ more.newStreams⟩)
        else (current, outputs, released)
  have stable (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (valid : acc.1.GroupErrorAccounting work failed)
      : (step acc group).1.GroupErrorAccounting work failed := by
    obtain ⟨current, outputs, released⟩ := acc
    dsimp only [step]
    split
    · exact valid
    · rename_i node found
      have updated := valid.putGroupNode { node with pending := node.pending - 1 }
        (valid.live node (List.mem_of_find?_eq_some found))
      split
      · exact updated.finishGroupSuccess _
      · exact updated
  unfold State.taskSuccess
  split
  · exact counts
  · rename_i taskNode found
    split
    · exact counts.removeTask occurrence
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have before : withValue.GroupErrorAccounting work failed := counts
    have integrated := before.maybeIntegrateWork result.work (some occurrence)
    have released := fold_preserves _ step taskNode.task.groups stable
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {}) integrated
    exact (released.startNewWork _).drainReadyGroups

/-- Stream-item integration and draining preserve complete group error totals.
Witness: every item uses the same fresh-key certificates and retains the prior failure list.
-/
theorem State.GroupErrorAccounting.streamItems {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.GroupErrorAccounting work failed := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    (pruned.startNewWork { more with newGroups := nonempty }, groups ++ nonempty,
      streams ++ more.newStreams, values ++ [item.value])
  have stable (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem)
      (valid : acc.1.GroupErrorAccounting work failed)
      : (step acc item).1.GroupErrorAccounting work failed :=
    ((valid.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  dsimp only [State.streamItems]
  split
  · exact counts
  · exact (fold_preserves _ step items stable (queue, [], [], []) counts).drainReadyGroups

/-- Every accepted matching event preserves complete eligible-failure accounting.
Witness: only an eligible task failure enlarges the inventory. Ignored task settlements
and stream events retain its exact prior total.
-/
theorem State.GroupErrorAccounting.handleGraphEvent {queue : State} {work failed}
    (counts : queue.GroupErrorAccounting work failed) (generated : ExecutedWork work)
    (live : queue.LiveGroupsRegistered) (covered : queue.TaskGroupsRegistered)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (source : event.MatchesWork work) (accepted : queue.acceptsGraphEvent event = true)
    : (queue.handleGraphEvent event).1.GroupErrorAccounting work
        (queue.objectFailureContribution event ++ failed) := by
  cases event with
  | taskSuccess occurrence result => exact counts.taskSuccess occurrence result
  | taskFailure occurrence errors =>
      cases found : queue.taskNode? occurrence with
      | none => simp [State.acceptsGraphEvent, found] at accepted
      | some task =>
          exact counts.taskFailure generated live covered registered matching occurrence errors
            task found source
  | streamItems stream items => exact counts.streamItems stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact counts
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact counts

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
