import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.Correctness.DependencyKeys
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedKeyRoles

/-! Uniqueness of live group keys across queue transitions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Concrete task bookkeeping
-----------------------------------------------------------------------------------------

/-- A successful key lookup returns the group node with that delivery key. -/
theorem State.groupNode?_key {queue : State} {key : Nat} {node : GroupNode}
    (found : queue.groupNode? key = some node)
    : node.group.node.key = key := by
  have selected := List.find?_some (p := fun candidate : GroupNode =>
    candidate.group.node.key == key) (by simpa [State.groupNode?] using found)
  exact beq_iff_eq.mp selected

/-- A live queue never stores two group nodes under the same delivery key. -/
def State.GroupKeysUnique (queue : State) : Prop :=
  (queue.groupNodes.map (fun node => node.group.node.key)).Nodup

/-- A unique delivery key identifies at most one live group node. -/
theorem State.GroupKeysUnique.sameNode {queue : State}
    (unique : queue.GroupKeysUnique) {first second : GroupNode}
    (firstMember : first ∈ queue.groupNodes)
    (secondMember : second ∈ queue.groupNodes)
    (sameKey : first.group.node.key = second.group.node.key)
    : first = second := by
  have helper (nodes : List GroupNode)
      (keysUnique : (nodes.map (fun node => node.group.node.key)).Nodup)
      {first second : GroupNode}
      (firstMember : first ∈ nodes) (secondMember : second ∈ nodes)
      (sameKey : first.group.node.key = second.group.node.key)
      : first = second := by
    induction nodes with
    | nil => cases firstMember
    | cons head tail ih =>
        obtain ⟨headAbsent, tailUnique⟩ := List.nodup_cons.mp keysUnique
        rcases List.mem_cons.mp firstMember with equalFirst | firstTail
        · subst first
          rcases List.mem_cons.mp secondMember with equalSecond | secondTail
          · exact equalSecond.symm
          · have inKeys : head.group.node.key ∈
                tail.map (fun node => node.group.node.key) :=
              List.mem_map.mpr ⟨second, secondTail, sameKey.symm⟩
            exact False.elim (headAbsent inKeys)
        · rcases List.mem_cons.mp secondMember with equalSecond | secondTail
          · subst second
            have inKeys : head.group.node.key ∈
                  tail.map (fun node => node.group.node.key) :=
              List.mem_map.mpr ⟨first, firstTail, sameKey⟩
            exact False.elim (headAbsent inKeys)
          · exact ih tailUnique firstTail secondTail
  exact helper queue.groupNodes unique firstMember secondMember sameKey

/-- A unique live group is returned by lookup at its own key.
Witness: any selected entry has the same key, so uniqueness identifies the records. -/
theorem State.GroupKeysUnique.groupNode?_of_mem {queue : State}
    (unique : queue.GroupKeysUnique) {node : GroupNode} (member : node ∈ queue.groupNodes)
    : queue.groupNode? node.group.node.key = some node := by
  cases found : queue.groupNode? node.group.node.key with
  | none =>
      have absent := List.find?_eq_none.mp found node member
      simp at absent
  | some selected =>
      have same := unique.sameNode (List.mem_of_find?_eq_some found) member
        (State.groupNode?_key found)
      exact congrArg some same

/-- Replacing nodes by key does not change the key list itself. -/
theorem State.putGroupNode_keys (queue : State) (updated : GroupNode)
    : (queue.putGroupNode updated).groupNodes.map (fun node => node.group.node.key)
      = queue.groupNodes.map (fun node => node.group.node.key) := by
  change ((queue.groupNodes.map
    (fun node => if node.group.node.key == updated.group.node.key then
      updated else node)).map (fun node => node.group.node.key)
      = queue.groupNodes.map (fun node => node.group.node.key))
  rw [List.map_map]
  apply List.map_congr_left
  intro node member
  by_cases same : node.group.node.key == updated.group.node.key
  · have equal := beq_iff_eq.mp same
    simp [equal]
  · have different : node.group.node.key ≠ updated.group.node.key := by
      intro equal
      exact same (beq_iff_eq.mpr equal)
    simp [different]

theorem State.GroupKeysUnique.putGroupNode {queue : State}
    (unique : queue.GroupKeysUnique) (updated : GroupNode)
    : (queue.putGroupNode updated).GroupKeysUnique := by
  change ((queue.putGroupNode updated).groupNodes.map
    (fun node => node.group.node.key)).Nodup
  rw [State.putGroupNode_keys]
  exact unique

/-- Registration preserves distinct live keys, also when a cancelled parent blocks it.
Witness: refusal leaves the node list unchanged; the appended key is fresh otherwise.
-/
theorem State.GroupKeysUnique.addGroup {queue : State}
    (unique : queue.GroupKeysUnique) (group : Group)
    : (queue.addGroup group).GroupKeysUnique := by
  unfold State.addGroup
  split
  · exact unique
  · rename_i absent
    have fresh : group.node.key ∉ queue.groupNodes.map
        (fun node => node.group.node.key) := by
      intro member
      obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp member
      have none : queue.groupNode? group.node.key = none := by
        exact (by simpa using absent :
          group.node.key ∉ queue.registeredGroups
            ∧ queue.groupNode? group.node.key = none).2
      have noMatch := (List.find?_eq_none.mp none) node nodeMember
      simp [same] at noMatch
    split
    · exact unique
    · change ((queue.groupNodes ++ [({ group } : GroupNode)]).map
        (fun node => node.group.node.key)).Nodup
      simpa [List.map_append, fresh] using List.nodup_append.mpr
        ⟨unique, by simp, by
          intro key earlier sameKey latest equal
          subst sameKey
          simp only [List.mem_singleton] at latest
          subst key
          exact fresh earlier⟩

/-- Parent links do not change group keys. -/
theorem State.GroupKeysUnique.addGroups {queue : State}
    (unique : queue.GroupKeysUnique) (groups : List Group)
    : (queue.addGroups groups).1.GroupKeysUnique := by
  let linkStep (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children :=
              if node.childGroups.contains group.node.key then
                node.childGroups
              else
                node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have linkUnique (current : State) (group : Group)
      (currentUnique : current.GroupKeysUnique)
      : (linkStep current group).GroupKeysUnique := by
    unfold linkStep
    cases parent : group.parent with
    | none => simpa only [parent] using currentUnique
    | some key =>
        cases found : current.groupNode? key with
        | none => simpa only [parent, found] using currentUnique
        | some node =>
            simp only [found]
            exact currentUnique.putGroupNode _
  have linkFold (more : List Group) :
      ∀ current, current.GroupKeysUnique →
        (more.foldl linkStep current).GroupKeysUnique := by
    induction more with
    | nil => intro current currentUnique; exact currentUnique
    | cons group rest ih =>
        intro current currentUnique
        exact ih (linkStep current group) (linkUnique current group currentUnique)
  have registerUnique (more : List Group) :
      (more.foldl State.addGroup queue).GroupKeysUnique := by
    induction more generalizing queue with
    | nil => exact unique
    | cons group rest ih =>
        simpa only [List.foldl_cons]
          using ih (queue := queue.addGroup group) (unique.addGroup group)
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).GroupKeysUnique
  exact linkFold fresh _ (registerUnique fresh)

/-- Task registration changes group metadata, never its key collection. -/
theorem State.GroupKeysUnique.addTask {queue : State}
    (unique : queue.GroupKeysUnique) (task : Task)
    : (queue.addTask task).GroupKeysUnique := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepUnique (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.GroupKeysUnique)
      : (step current group).GroupKeysUnique := by
    unfold step
    split
    · exact currentUnique
    · split
      · exact currentUnique
      · exact currentUnique.putGroupNode _
  have foldUnique (groups : List Execution.DeliveryNode) :
      ∀ current, current.GroupKeysUnique →
        (groups.foldl step current).GroupKeysUnique := by
    induction groups with
    | nil => intro current currentUnique; exact currentUnique
    | cons group rest ih =>
        intro current currentUnique
        exact ih (step current group) (stepUnique current group currentUnique)
  let current := task.groups.foldl step registered
  have currentUnique : current.GroupKeysUnique :=
    foldUnique task.groups registered unique
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).GroupKeysUnique
  split <;> exact currentUnique

/-- Stream descriptors do not alter the live group-node map. -/
theorem State.GroupKeysUnique.addStreams {queue : State}
    (unique : queue.GroupKeysUnique) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.GroupKeysUnique := by
  let fresh :=
    streams.foldl
      (fun selected stream =>
        if (queue.stream? stream.node.key).isSome
            || selected.any (fun known => known.node.key == stream.node.key) then
          selected
        else
          selected ++ [stream])
      []
  let current : State := { queue with streams := queue.streams ++ fresh }
  have currentUnique : current.GroupKeysUnique := unique
  cases parentTask with
  | none => exact currentUnique
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentUnique

/-- Integrating new work registers groups once and only updates existing
group-node metadata thereafter.
-/
theorem State.GroupKeysUnique.maybeIntegrateWork {queue : State}
    (unique : queue.GroupKeysUnique) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.GroupKeysUnique := by
  let withGroups := (queue.addGroups work.groups).1
  let withTasks := work.tasks.foldl State.addTask withGroups
  have taskFold (tasks : List Task) :
      ∀ current, current.GroupKeysUnique →
        (tasks.foldl State.addTask current).GroupKeysUnique := by
    induction tasks with
    | nil => intro current currentUnique; exact currentUnique
    | cons task rest ih =>
        intro current currentUnique
        exact ih (current.addTask task) (currentUnique.addTask task)
  have taskUnique : withTasks.GroupKeysUnique :=
    taskFold work.tasks withGroups (unique.addGroups work.groups)
  change (withTasks.addStreams work.streams parentTask).1.GroupKeysUnique
  exact taskUnique.addStreams work.streams parentTask

/-- Removing empty group shells retains a subset of unique keys. -/
theorem State.GroupKeysUnique.pruneEmptyGroups {queue : State}
    (unique : queue.GroupKeysUnique) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupKeysUnique := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentUnique : current.GroupKeysUnique)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupKeysUnique := by
    induction fuel generalizing current remaining kept with
    | zero => exact currentUnique
    | succ fuel ih =>
        cases remaining with
        | nil => exact currentUnique
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentUnique
            · split
              · apply ih
                change ((current.groupNodes.filter
                  (fun node => node.group.node.key != group.key)).map
                    (fun node => node.group.node.key)).Nodup
                have mapped : (current.groupNodes.filter
                    (fun node => node.group.node.key != group.key)).map
                      (fun node => node.group.node.key)
                    = (current.groupNodes.map
                      (fun node => node.group.node.key)).filter
                        (fun key => key != group.key) :=
                  (List.filter_map
                    (p := fun key => key != group.key)
                    (f := fun node : GroupNode => node.group.node.key)).symm
                rw [mapped]
                exact currentUnique.filter _
              · exact ih _ _ _ currentUnique
  exact loop _ queue groups [] unique

/-- Every retained notice still has nonempty task membership or a cached failure.
Witness: pruning never removes a previously retained nonempty record with the same key;
key uniqueness identifies it with the lookup that would otherwise remove it. The result
keeps the actual post-pruning record, not merely the notice's key or a pending count.
-/
theorem State.pruneEmptyGroups_keptContents
    (queue : State) (groups : List Execution.DeliveryNode)
    (unique : queue.GroupKeysUnique)
    : ∀ key ∈ (queue.pruneEmptyGroups groups).2.map Execution.DeliveryNode.key,
        ∃ node ∈ (queue.pruneEmptyGroups groups).1.groupNodes,
          node.group.node.key = key
          ∧ (node.tasks.isEmpty && node.failure.isNone) ≠ true := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentUnique : current.GroupKeysUnique)
      (keptPresent : ∀ key ∈ kept.map Execution.DeliveryNode.key,
        ∃ node ∈ current.groupNodes,
          node.group.node.key = key ∧ (node.tasks.isEmpty && node.failure.isNone) ≠ true)
      : ∀ key ∈ (State.pruneEmptyGroups.go fuel current remaining kept).2.map
          Execution.DeliveryNode.key,
          ∃ node ∈ (State.pruneEmptyGroups.go fuel current remaining kept).1.groupNodes,
            node.group.node.key = key
            ∧ (node.tasks.isEmpty && node.failure.isNone) ≠ true := by
    induction fuel generalizing current remaining kept with
    | zero => exact keptPresent
    | succ fuel ih =>
        cases remaining with
        | nil => exact keptPresent
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            cases found : current.groupNode? group.key with
            | none => exact ih _ _ _ currentUnique keptPresent
            | some node =>
                by_cases zero : (node.tasks.isEmpty && node.failure.isNone) = true
                · simp only [zero, ite_true]
                  let next : State :=
                    {
                      current with
                        groupNodes := current.groupNodes.filter
                          (fun entry => entry.group.node.key != group.key)
                    }
                  have nextUnique : next.GroupKeysUnique := by
                    change ((current.groupNodes.filter
                      (fun entry => entry.group.node.key != group.key)).map
                        (fun entry => entry.group.node.key)).Nodup
                    have mapped :
                        (current.groupNodes.filter
                          (fun entry => entry.group.node.key != group.key)).map
                            (fun entry => entry.group.node.key)
                          = (current.groupNodes.map
                            (fun entry => entry.group.node.key)).filter
                              (fun key => key != group.key) :=
                      (List.filter_map
                        (p := fun key => key != group.key)
                        (f := fun entry : GroupNode => entry.group.node.key)).symm
                    rw [mapped]
                    exact currentUnique.filter _
                  have nextPresent : ∀ key ∈ kept.map Execution.DeliveryNode.key,
                      ∃ entry ∈ next.groupNodes,
                        entry.group.node.key = key
                          ∧ (entry.tasks.isEmpty && entry.failure.isNone) ≠ true := by
                    intro key member
                    obtain ⟨entry, entryMember, same, positive⟩ :=
                      keptPresent key member
                    have different : entry.group.node.key ≠ group.key := by
                      intro equal
                      have sameNode : entry = node :=
                        currentUnique.sameNode entryMember
                          (List.mem_of_find?_eq_some found)
                          (equal.trans (current.groupNode?_key found).symm)
                      subst entry
                      exact positive zero
                    refine ⟨entry, ?_, same, positive⟩
                    exact List.mem_filter.mpr
                      ⟨entryMember, by simp [bne, different]⟩
                  exact ih _ _ _ nextUnique nextPresent
                · simp only [zero]
                  have nextPresent :
                      ∀ key ∈ (kept ++ [group]).map Execution.DeliveryNode.key,
                        ∃ entry ∈ current.groupNodes,
                          entry.group.node.key = key
                            ∧ (entry.tasks.isEmpty && entry.failure.isNone) ≠ true := by
                    intro key member
                    rw [List.map_append, List.mem_append] at member
                    rcases member with old | added
                    · exact keptPresent key old
                    · have equal : key = group.key := by simpa using added
                      subst key
                      exact ⟨node, List.mem_of_find?_eq_some found,
                        current.groupNode?_key found, zero⟩
                  exact ih _ _ _ currentUnique nextPresent
  have empty : ∀ key ∈ ([] : List Execution.DeliveryNode).map
      Execution.DeliveryNode.key,
      ∃ node ∈ queue.groupNodes,
        node.group.node.key = key ∧ (node.tasks.isEmpty && node.failure.isNone) ≠ true := by
    intro key member
    cases member
  exact loop _ queue groups [] unique empty

/-- Every nonempty group retained by pruning still has a live group node.
Witness: project key presence from the stronger post-pruning contents certificate.
The result records input descriptors, so only key presence is asserted here.
-/
theorem State.pruneEmptyGroups_keptPresent
    (queue : State) (groups : List Execution.DeliveryNode)
    (unique : queue.GroupKeysUnique)
    : ∀ key ∈ (queue.pruneEmptyGroups groups).2.map Execution.DeliveryNode.key,
        key
        ∈ (queue.pruneEmptyGroups groups).1.groupNodes.map
            (fun node => node.group.node.key) := by
  intro key member
  obtain ⟨node, present, same, _⟩ := queue.pruneEmptyGroups_keptContents groups unique key member
  exact List.mem_map.mpr ⟨node, present, same⟩

/-- Activating root tasks and streams does not modify the group-node map. -/
theorem State.GroupKeysUnique.startNewWork {queue : State}
    (unique : queue.GroupKeysUnique) (newWork : NewWork)
    : (queue.startNewWork newWork).GroupKeysUnique := by
  let groups := newWork.newGroups.map Execution.DeliveryNode.key
  let streams := newWork.newStreams.map Execution.DeliveryNode.key
  let current : State := { queue with rootGroups := queue.rootGroups ++ groups }
  have groupFold (keys : Keys) :
      ∀ current, current.GroupKeysUnique →
        (keys.foldl State.startGroup current).GroupKeysUnique := by
    induction keys with
    | nil => intro current currentUnique; exact currentUnique
    | cons key rest ih =>
        intro current currentUnique
        apply ih (current.startGroup key)
        unfold State.startGroup
        split
        · exact currentUnique
        · rename_i node found
          have taskFold (tasks : List Occurrence) :
              ∀ current, current.GroupKeysUnique →
                (tasks.foldl State.startTask current).GroupKeysUnique := by
            induction tasks with
            | nil => intro current balanced; exact balanced
            | cons task rest next =>
                intro current balanced
                apply next (current.startTask task)
                unfold State.startTask
                split
                · exact balanced
                · split <;> exact balanced
          split
          · exact currentUnique
          · exact taskFold node.tasks current currentUnique
  have streamFold (keys : Keys) :
      ∀ current, current.GroupKeysUnique →
        (keys.foldl State.startStream current).GroupKeysUnique := by
    induction keys with
    | nil => intro current currentUnique; exact currentUnique
    | cons key rest ih =>
        intro current currentUnique
        apply ih (current.startStream key)
        unfold State.startStream
        split <;> exact currentUnique
  change (streams.foldl State.startStream
    (groups.foldl State.startGroup current)).GroupKeysUnique
  exact streamFold streams _ (groupFold groups current unique)

/-- Queue initialization has at most one live group node per delivery key. -/
theorem createWorkQueue_groupKeysUnique (work : Work)
    : (State.initialize work).GroupKeysUnique := by
  let integrated := (({} : State).maybeIntegrateWork work).1
  let newWork := (({} : State).maybeIntegrateWork work).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
  have emptyUnique : ({} : State).GroupKeysUnique := by simp [State.GroupKeysUnique]
  have integratedUnique : integrated.GroupKeysUnique :=
    emptyUnique.maybeIntegrateWork work
  have prunedUnique : pruned.GroupKeysUnique :=
    integratedUnique.pruneEmptyGroups newWork.newGroups
  have startedUnique : started.GroupKeysUnique := prunedUnique.startNewWork roots
  change State.GroupKeysUnique
    { started with initialGroups := groups, initialStreams := roots.newStreams }
  exact startedUnique

/-- Filtering the group-node map can only remove key occurrences. -/
theorem State.GroupKeysUnique.filterGroupNodes {queue : State}
    (unique : queue.GroupKeysUnique) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep }).GroupKeysUnique := by
  change ((queue.groupNodes.filter keep).map
    (fun node => node.group.node.key)).Nodup
  exact List.Nodup.sublist ((List.filter_sublist).map _) unique

/-- Flushing a task removes memberships but keeps the group-key list. -/
theorem State.GroupKeysUnique.removeTask {queue : State}
    (unique : queue.GroupKeysUnique) (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupKeysUnique := by
  change ((queue.groupNodes.map
    (fun node => { node with tasks := node.tasks.filter (· != occurrence) })).map
      (fun node => node.group.node.key)).Nodup
  simpa [List.map_map, Function.comp_def, State.GroupKeysUnique] using unique

/-- Cancelling a group and its descendants retains a filtered key subset. -/
theorem State.GroupKeysUnique.removeGroup {queue : State}
    (unique : queue.GroupKeysUnique) (key : Nat)
    : (queue.removeGroup key).GroupKeysUnique := by
  unfold State.removeGroup
  exact unique.filterGroupNodes _

/-- Flushing a successful group preserves unique keys while removing shared
memberships, its own node, and possibly empty descendants.
-/
theorem State.GroupKeysUnique.finishGroupSuccess {queue : State}
    (unique : queue.GroupKeysUnique) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupKeysUnique := by
  let step (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values :=
          match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have stepUnique (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) (currentUnique : acc.1.GroupKeysUnique)
      : (step acc occurrence).1.GroupKeysUnique := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentUnique
    · exact currentUnique.removeTask occurrence
  have foldUnique (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × Keys,
        acc.1.GroupKeysUnique → (tasks.foldl step acc).1.GroupKeysUnique := by
    induction tasks with
    | nil => intro acc currentUnique; exact currentUnique
    | cons occurrence rest ih =>
        intro acc currentUnique
        exact ih (step acc occurrence) (stepUnique acc occurrence currentUnique)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedUnique : flushed.GroupKeysUnique :=
    foldUnique group.tasks (queue, [], []) unique
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.key != group.group.node.key)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentUnique : current.GroupKeysUnique :=
    flushedUnique.filterGroupNodes _
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.GroupKeysUnique
  exact currentUnique.pruneEmptyGroups children

/-- Every group key released by a successful group flush still has a live
node after empty-child pruning. -/
theorem State.finishGroupSuccess_newGroupsPresent
    {queue : State} (unique : queue.GroupKeysUnique) (group : GroupNode)
    : ∀ key ∈
        (queue.finishGroupSuccess group).2.2.newGroups.map Execution.DeliveryNode.key,
        key
        ∈ (queue.finishGroupSuccess group).1.groupNodes.map
            (fun node => node.group.node.key) := by
  let step (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values :=
          match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have stepUnique (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) (currentUnique : acc.1.GroupKeysUnique)
      : (step acc occurrence).1.GroupKeysUnique := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentUnique
    · exact currentUnique.removeTask occurrence
  have foldUnique (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × Keys,
        acc.1.GroupKeysUnique → (tasks.foldl step acc).1.GroupKeysUnique := by
    induction tasks with
    | nil => intro acc currentUnique; exact currentUnique
    | cons occurrence rest ih =>
        intro acc currentUnique
        exact ih (step acc occurrence) (stepUnique acc occurrence currentUnique)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedUnique : flushed.GroupKeysUnique :=
    foldUnique group.tasks (queue, [], []) unique
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.key != group.group.node.key)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentUnique : current.GroupKeysUnique :=
    flushedUnique.filterGroupNodes _
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  change ∀ key ∈ (current.pruneEmptyGroups children).2.map
      Execution.DeliveryNode.key,
      key ∈ (current.pruneEmptyGroups children).1.groupNodes.map
        (fun node => node.group.node.key)
  exact current.pruneEmptyGroups_keptPresent children currentUnique

/-- Failing a group retains only a filtered subset of live group keys. -/
theorem State.GroupKeysUnique.finishGroupFailure {queue : State}
    (unique : queue.GroupKeysUnique) (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.GroupKeysUnique :=
  unique.removeGroup group.group.node.key

/-- Draining ready groups cannot duplicate a live key.
Witness: induction over the drain bound, using closure and activation preservation.
-/
theorem State.GroupKeysUnique.drainReadyGroups {queue : State}
    (unique : queue.GroupKeysUnique)
    : queue.drainReadyGroups.1.GroupKeysUnique := by
  have loop (fuel : Nat) (current : State) (unique : current.GroupKeysUnique)
      : (State.drainReadyGroups.go fuel current).1.GroupKeysUnique := by
    induction fuel generalizing current with
    | zero => exact unique
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact unique
        · rename_i node found
          cases failure : node.failure with
          | none =>
              exact ih _ ((unique.finishGroupSuccess node).startNewWork _)
          | some errors => exact ih _ (unique.finishGroupFailure node errors)
  exact loop _ queue unique

/-- A failed task closes active owners or retains latent errors without duplicating keys.
Witness: task removal and each owner update preserve key uniqueness.
-/
theorem State.GroupKeysUnique.taskFailure {queue : State}
    (unique : queue.GroupKeysUnique) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.GroupKeysUnique := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent :=
    let (current, events) := acc
    match current.groupNode? group.key with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.key then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else
          (current.putGroupNode
            {
              node with
                pending := node.pending - 1
                failure := some (node.failure.getD 0 + errors)
            }, events)
  have stepUnique (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentUnique : acc.1.GroupKeysUnique)
      : (step acc group).1.GroupKeysUnique := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    cases found : current.groupNode? group.key with
    | none => exact currentUnique
    | some node =>
        by_cases started : current.rootGroups.contains group.key = true
        · simp only [started, ite_true]
          exact currentUnique.finishGroupFailure node errors
        · simp only [started]
          exact currentUnique.putGroupNode _
  have foldUnique (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupKeysUnique → (groups.foldl step acc).1.GroupKeysUnique := by
    induction groups with
    | nil => intro acc currentUnique; exact currentUnique
    | cons group rest ih =>
        intro acc currentUnique
        exact ih (step acc group) (stepUnique acc group currentUnique)
  unfold State.taskFailure
  split
  · exact unique
  · rename_i taskNode found
    split <;> try exact unique.removeTask occurrence
    let current := queue.removeTask occurrence
    have currentUnique : current.GroupKeysUnique := unique.removeTask occurrence
    change (taskNode.task.groups.foldl step (current, [])).1.GroupKeysUnique
    exact foldUnique taskNode.task.groups (current, []) currentUnique

/-- Successful stream-item integration preserves unique group keys. -/
theorem State.GroupKeysUnique.streamItems {queue : State}
    (unique : queue.GroupKeysUnique) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.GroupKeysUnique := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (
      pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty,
      streams ++ newWork.newStreams,
      values ++ [item.value]
    )
  have stepUnique (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) (currentUnique : acc.1.GroupKeysUnique)
      : (step acc item).1.GroupKeysUnique := by
    obtain ⟨current, groups, streams, values⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedUnique : integrated.1.GroupKeysUnique :=
      currentUnique.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedUnique : pruned.1.GroupKeysUnique :=
      integratedUnique.pruneEmptyGroups integrated.2.newGroups
    exact prunedUnique.startNewWork { integrated.2 with newGroups := pruned.2 }
  have foldUnique (more : List StreamItem) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue,
        acc.1.GroupKeysUnique → (more.foldl step acc).1.GroupKeysUnique := by
    induction more with
    | nil => intro acc currentUnique; exact currentUnique
    | cons item rest ih =>
        intro acc currentUnique
        exact ih (step acc item) (stepUnique acc item currentUnique)
  dsimp only [State.streamItems]
  split
  · exact unique
  · exact (foldUnique items (queue, [], [], []) unique).drainReadyGroups

/-- Stream closure does not touch the group-node map. -/
theorem State.GroupKeysUnique.streamSuccess {queue : State}
    (unique : queue.GroupKeysUnique) (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.GroupKeysUnique := by
  unfold State.streamSuccess
  split <;> exact unique

/-- Failed stream closure does not touch the group-node map either. -/
theorem State.GroupKeysUnique.streamFailure {queue : State}
    (unique : queue.GroupKeysUnique) (stream : Execution.DeliveryNode)
    (errors : Nat)
    : (queue.streamFailure stream errors).1.GroupKeysUnique := by
  unfold State.streamFailure
  split <;> exact unique

/-- Task success integrates child work, updates contributor counters, and may
flush completed groups; each stage preserves unique live group keys.
-/
theorem State.GroupKeysUnique.taskSuccess {queue : State}
    (unique : queue.GroupKeysUnique) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.GroupKeysUnique := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have settleUnique (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.GroupKeysUnique)
      : (settleStep current group).GroupKeysUnique := by
    unfold settleStep
    split
    · exact currentUnique
    · exact currentUnique.putGroupNode _
  let releaseStep (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent × NewWork :=
    let (current, events, released) := acc
    match current.groupNode? group.key with
    | none => (current, events, released)
    | some node =>
        let node := { node with pending := node.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.key && node.pending == 0
            && node.failure.isNone then
          let (next, finished, newWork) := current.finishGroupSuccess node
          (
            next,
            events ++ finished,
            ⟨
              released.newGroups ++ newWork.newGroups,
              released.newStreams ++ newWork.newStreams
            ⟩
          )
        else
          (current, events, released)
  have releaseUnique (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) (currentUnique : acc.1.GroupKeysUnique)
      : (releaseStep acc group).1.GroupKeysUnique := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [releaseStep]
    split
    · exact currentUnique
    · rename_i node found
      have decremented : (current.putGroupNode
          { node with pending := node.pending - 1 }).GroupKeysUnique := by
        simpa only [settleStep, found] using settleUnique current group currentUnique
      split
      · exact decremented.finishGroupSuccess _
      · exact decremented
  have releaseFold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.GroupKeysUnique → (groups.foldl releaseStep acc).1.GroupKeysUnique := by
    induction groups with
    | nil => intro acc currentUnique; exact currentUnique
    | cons group rest ih =>
        intro acc currentUnique
        exact ih (releaseStep acc group) (releaseUnique acc group currentUnique)
  unfold State.taskSuccess
  split
  · exact unique
  · rename_i taskNode found
    split <;> try exact unique.removeTask occurrence
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have withValueUnique : withValue.GroupKeysUnique := unique
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedUnique : integrated.GroupKeysUnique :=
      withValueUnique.maybeIntegrateWork result.work (some occurrence)
    let finished := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have finishedUnique : finished.1.GroupKeysUnique :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedUnique
    change (finished.1.startNewWork finished.2.2).drainReadyGroups.1.GroupKeysUnique
    exact (finishedUnique.startNewWork finished.2.2).drainReadyGroups

/-- Every individual host event preserves unique live group keys. -/
theorem State.GroupKeysUnique.handleGraphEvent {queue : State}
    (unique : queue.GroupKeysUnique) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.GroupKeysUnique := by
  cases event with
  | taskSuccess occurrence result => exact unique.taskSuccess occurrence result
  | taskFailure occurrence errors => exact unique.taskFailure occurrence errors
  | streamItems stream items => exact unique.streamItems stream items
  | streamSuccess stream => exact unique.streamSuccess stream
  | streamFailure stream errors => exact unique.streamFailure stream errors

/-- Every available host batch preserves unique live group keys. -/
theorem State.GroupKeysUnique.handleGraphEvents {queue : State}
    (unique : queue.GroupKeysUnique) (batch : List GraphEvent)
    : (queue.handleGraphEvents batch).1.GroupKeysUnique := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have foldUnique (events : List GraphEvent) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupKeysUnique → (events.foldl step acc).1.GroupKeysUnique := by
    induction events with
    | nil => intro acc currentUnique; exact currentUnique
    | cons event rest ih =>
        intro acc currentUnique
        obtain ⟨current, outputs⟩ := acc
        have nextUnique : (step (current, outputs) event).1.GroupKeysUnique :=
          currentUnique.handleGraphEvent event
        exact ih (step (current, outputs) event) nextUnique
  unfold State.handleGraphEvents
  split
  · exact unique
  · cases outcome : batch.foldl step (queue, []) with
    | mk current outputs =>
        have currentUnique : current.GroupKeysUnique := by
          have folded := foldUnique batch (queue, []) unique
          rw [outcome] at folded
          exact folded
        dsimp only
        split <;> exact currentUnique

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
