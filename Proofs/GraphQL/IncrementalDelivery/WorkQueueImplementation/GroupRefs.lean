import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.Correctness.DependencyRefs
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedRefRoles

/-! Uniqueness of live group refs across queue transitions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Concrete task bookkeeping
-----------------------------------------------------------------------------------------

/-- A successful ref lookup returns the group node with that delivery ref. -/
theorem State.groupNode?_ref {queue : State} {ref : NodeRef} {node : GroupNode}
    (found : queue.groupNode? ref = some node)
    : node.group.node.ref = ref := by
  have selected := List.find?_some (p := fun candidate : GroupNode =>
    candidate.group.node.ref == ref) (by simpa [State.groupNode?] using found)
  exact beq_iff_eq.mp selected

/-- A live queue never stores two group nodes under the same delivery ref. -/
def State.GroupRefsUnique (queue : State) : Prop :=
  (queue.groupNodes.map (fun node => node.group.node.ref)).Nodup

/-- A unique delivery ref identifies at most one live group node. -/
theorem State.GroupRefsUnique.sameNode {queue : State}
    (unique : queue.GroupRefsUnique) {first second : GroupNode}
    (firstMember : first ∈ queue.groupNodes)
    (secondMember : second ∈ queue.groupNodes)
    (sameRef : first.group.node.ref = second.group.node.ref)
    : first = second := by
  have helper (nodes : List GroupNode)
      (refsUnique : (nodes.map (fun node => node.group.node.ref)).Nodup)
      {first second : GroupNode}
      (firstMember : first ∈ nodes) (secondMember : second ∈ nodes)
      (sameRef : first.group.node.ref = second.group.node.ref)
      : first = second := by
    induction nodes with
    | nil => cases firstMember
    | cons head tail ih =>
        obtain ⟨headAbsent, tailUnique⟩ := List.nodup_cons.mp refsUnique
        rcases List.mem_cons.mp firstMember with equalFirst | firstTail
        · subst first
          rcases List.mem_cons.mp secondMember with equalSecond | secondTail
          · exact equalSecond.symm
          · have inRefs : head.group.node.ref ∈
                tail.map (fun node => node.group.node.ref) :=
              List.mem_map.mpr ⟨second, secondTail, sameRef.symm⟩
            exact False.elim (headAbsent inRefs)
        · rcases List.mem_cons.mp secondMember with equalSecond | secondTail
          · subst second
            have inRefs : head.group.node.ref ∈
                  tail.map (fun node => node.group.node.ref) :=
              List.mem_map.mpr ⟨first, firstTail, sameRef⟩
            exact False.elim (headAbsent inRefs)
          · exact ih tailUnique firstTail secondTail
  exact helper queue.groupNodes unique firstMember secondMember sameRef

/-- A unique live group is returned by lookup at its own ref.
Witness: any selected entry has the same ref, so uniqueness identifies the records. -/
theorem State.GroupRefsUnique.groupNode?_of_mem {queue : State}
    (unique : queue.GroupRefsUnique) {node : GroupNode} (member : node ∈ queue.groupNodes)
    : queue.groupNode? node.group.node.ref = some node := by
  cases found : queue.groupNode? node.group.node.ref with
  | none =>
      have absent := List.find?_eq_none.mp found node member
      simp at absent
  | some selected =>
      have same := unique.sameNode (List.mem_of_find?_eq_some found) member
        (State.groupNode?_ref found)
      exact congrArg some same

/-- Replacing nodes by ref does not change the ref list itself. -/
theorem State.putGroupNode_refs (queue : State) (updated : GroupNode)
    : (queue.putGroupNode updated).groupNodes.map (fun node => node.group.node.ref)
      = queue.groupNodes.map (fun node => node.group.node.ref) := by
  change ((queue.groupNodes.map
    (fun node => if node.group.node.ref == updated.group.node.ref then
      updated else node)).map (fun node => node.group.node.ref)
      = queue.groupNodes.map (fun node => node.group.node.ref))
  rw [List.map_map]
  apply List.map_congr_left
  intro node member
  by_cases same : node.group.node.ref == updated.group.node.ref
  · have equal := beq_iff_eq.mp same
    simp [equal]
  · have different : node.group.node.ref ≠ updated.group.node.ref := by
      intro equal
      exact same (beq_iff_eq.mpr equal)
    simp [different]

theorem State.GroupRefsUnique.putGroupNode {queue : State}
    (unique : queue.GroupRefsUnique) (updated : GroupNode)
    : (queue.putGroupNode updated).GroupRefsUnique := by
  change ((queue.putGroupNode updated).groupNodes.map
    (fun node => node.group.node.ref)).Nodup
  rw [State.putGroupNode_refs]
  exact unique

/-- Registration preserves distinct live refs, also when a cancelled parent blocks it.
Witness: refusal leaves the node list unchanged; the appended ref is fresh otherwise.
-/
theorem State.GroupRefsUnique.addGroup {queue : State}
    (unique : queue.GroupRefsUnique) (group : Group)
    : (queue.addGroup group).GroupRefsUnique := by
  unfold State.addGroup
  split
  · exact unique
  · rename_i absent
    have fresh : group.node.ref ∉ queue.groupNodes.map
        (fun node => node.group.node.ref) := by
      intro member
      obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp member
      have none : queue.groupNode? group.node.ref = none := by
        exact (by simpa using absent :
          group.node.ref ∉ queue.registeredGroups
            ∧ queue.groupNode? group.node.ref = none).2
      have noMatch := (List.find?_eq_none.mp none) node nodeMember
      simp [same] at noMatch
    split
    · exact unique
    · change ((queue.groupNodes ++ [({ group } : GroupNode)]).map
        (fun node => node.group.node.ref)).Nodup
      simpa [List.map_append, fresh] using List.nodup_append.mpr
        ⟨unique, by simp, by
          intro ref earlier sameRef latest equal
          subst sameRef
          simp only [List.mem_singleton] at latest
          subst ref
          exact fresh earlier⟩

/-- Parent links do not change group refs. -/
theorem State.GroupRefsUnique.addGroups {queue : State}
    (unique : queue.GroupRefsUnique) (groups : List Group)
    : (queue.addGroups groups).1.GroupRefsUnique := by
  let linkStep (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children :=
              if node.childGroups.contains group.node.ref then
                node.childGroups
              else
                node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have linkUnique (current : State) (group : Group)
      (currentUnique : current.GroupRefsUnique)
      : (linkStep current group).GroupRefsUnique := by
    unfold linkStep
    cases parent : group.parent with
    | none => simpa only [parent] using currentUnique
    | some ref =>
        cases found : current.groupNode? ref with
        | none => simpa only [parent, found] using currentUnique
        | some node =>
            simp only [found]
            exact currentUnique.putGroupNode _
  have linkFold (more : List Group) :
      ∀ current, current.GroupRefsUnique →
        (more.foldl linkStep current).GroupRefsUnique := by
    induction more with
    | nil => intro current currentUnique; exact currentUnique
    | cons group rest ih =>
        intro current currentUnique
        exact ih (linkStep current group) (linkUnique current group currentUnique)
  have registerUnique (more : List Group) :
      (more.foldl State.addGroup queue).GroupRefsUnique := by
    induction more generalizing queue with
    | nil => exact unique
    | cons group rest ih =>
        simpa only [List.foldl_cons]
          using ih (queue := queue.addGroup group) (unique.addGroup group)
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  change (fresh.foldl linkStep (fresh.foldl State.addGroup queue)).GroupRefsUnique
  exact linkFold fresh _ (registerUnique fresh)

/-- Task registration changes group metadata, never its ref collection. -/
theorem State.GroupRefsUnique.addTask {queue : State}
    (unique : queue.GroupRefsUnique) (task : Task)
    : (queue.addTask task).GroupRefsUnique := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then
          current
        else
          current.putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stepUnique (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.GroupRefsUnique)
      : (step current group).GroupRefsUnique := by
    unfold step
    split
    · exact currentUnique
    · split
      · exact currentUnique
      · exact currentUnique.putGroupNode _
  have foldUnique (groups : List Execution.DeliveryNode) :
      ∀ current, current.GroupRefsUnique →
        (groups.foldl step current).GroupRefsUnique := by
    induction groups with
    | nil => intro current currentUnique; exact currentUnique
    | cons group rest ih =>
        intro current currentUnique
        exact ih (step current group) (stepUnique current group currentUnique)
  let current := task.groups.foldl step registered
  have currentUnique : current.GroupRefsUnique :=
    foldUnique task.groups registered unique
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).GroupRefsUnique
  split <;> exact currentUnique

/-- Stream descriptors do not alter the live group-node map. -/
theorem State.GroupRefsUnique.addStreams {queue : State}
    (unique : queue.GroupRefsUnique) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.GroupRefsUnique := by
  let fresh :=
    streams.foldl
      (fun selected stream =>
        if (queue.stream? stream.node.ref).isSome
            || selected.any (fun known => known.node.ref == stream.node.ref) then
          selected
        else
          selected ++ [stream])
      []
  let current : State := { queue with streams := queue.streams ++ fresh }
  have currentUnique : current.GroupRefsUnique := unique
  cases parentTask with
  | none => exact currentUnique
  | some occurrence =>
      simp only [State.addStreams]
      split <;> exact currentUnique

/-- Integrating new work registers groups once and only updates existing
group-node metadata thereafter.
-/
theorem State.GroupRefsUnique.maybeIntegrateWork {queue : State}
    (unique : queue.GroupRefsUnique) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.GroupRefsUnique := by
  let withGroups := (queue.addGroups work.groups).1
  let withTasks := work.tasks.foldl State.addTask withGroups
  have taskFold (tasks : List Task) :
      ∀ current, current.GroupRefsUnique →
        (tasks.foldl State.addTask current).GroupRefsUnique := by
    induction tasks with
    | nil => intro current currentUnique; exact currentUnique
    | cons task rest ih =>
        intro current currentUnique
        exact ih (current.addTask task) (currentUnique.addTask task)
  have taskUnique : withTasks.GroupRefsUnique :=
    taskFold work.tasks withGroups (unique.addGroups work.groups)
  change (withTasks.addStreams work.streams parentTask).1.GroupRefsUnique
  exact taskUnique.addStreams work.streams parentTask

/-- Removing empty group shells retains a subset of unique refs. -/
theorem State.GroupRefsUnique.pruneEmptyGroups {queue : State}
    (unique : queue.GroupRefsUnique) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupRefsUnique := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentUnique : current.GroupRefsUnique)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupRefsUnique := by
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
                  (fun node => node.group.node.ref != group.ref)).map
                    (fun node => node.group.node.ref)).Nodup
                have mapped : (current.groupNodes.filter
                    (fun node => node.group.node.ref != group.ref)).map
                      (fun node => node.group.node.ref)
                    = (current.groupNodes.map
                      (fun node => node.group.node.ref)).filter
                        (fun ref => ref != group.ref) :=
                  (List.filter_map
                    (p := fun ref => ref != group.ref)
                    (f := fun node : GroupNode => node.group.node.ref)).symm
                rw [mapped]
                exact currentUnique.filter _
              · exact ih _ _ _ currentUnique
  exact loop _ queue groups [] unique

/-- Every retained notice still has nonempty task membership or a cached failure.
Witness: pruning never removes a previously retained nonempty record with the same ref;
ref uniqueness identifies it with the lookup that would otherwise remove it. The result
keeps the actual post-pruning record, not merely the notice's ref or a pending count.
-/
theorem State.pruneEmptyGroups_keptContents
    (queue : State) (groups : List Execution.DeliveryNode)
    (unique : queue.GroupRefsUnique)
    : ∀ ref ∈ (queue.pruneEmptyGroups groups).2.map Execution.DeliveryNode.ref,
        ∃ node ∈ (queue.pruneEmptyGroups groups).1.groupNodes,
          node.group.node.ref = ref
          ∧ (node.tasks.isEmpty && node.failure.isNone) ≠ true := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (currentUnique : current.GroupRefsUnique)
      (keptPresent : ∀ ref ∈ kept.map Execution.DeliveryNode.ref,
        ∃ node ∈ current.groupNodes,
          node.group.node.ref = ref ∧ (node.tasks.isEmpty && node.failure.isNone) ≠ true)
      : ∀ ref ∈ (State.pruneEmptyGroups.go fuel current remaining kept).2.map
          Execution.DeliveryNode.ref,
          ∃ node ∈ (State.pruneEmptyGroups.go fuel current remaining kept).1.groupNodes,
            node.group.node.ref = ref
            ∧ (node.tasks.isEmpty && node.failure.isNone) ≠ true := by
    induction fuel generalizing current remaining kept with
    | zero => exact keptPresent
    | succ fuel ih =>
        cases remaining with
        | nil => exact keptPresent
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            cases found : current.groupNode? group.ref with
            | none => exact ih _ _ _ currentUnique keptPresent
            | some node =>
                by_cases zero : (node.tasks.isEmpty && node.failure.isNone) = true
                · simp only [zero, ite_true]
                  let next : State :=
                    {
                      current with
                        groupNodes := current.groupNodes.filter
                          (fun entry => entry.group.node.ref != group.ref)
                    }
                  have nextUnique : next.GroupRefsUnique := by
                    change ((current.groupNodes.filter
                      (fun entry => entry.group.node.ref != group.ref)).map
                        (fun entry => entry.group.node.ref)).Nodup
                    have mapped :
                        (current.groupNodes.filter
                          (fun entry => entry.group.node.ref != group.ref)).map
                            (fun entry => entry.group.node.ref)
                          = (current.groupNodes.map
                            (fun entry => entry.group.node.ref)).filter
                              (fun ref => ref != group.ref) :=
                      (List.filter_map
                        (p := fun ref => ref != group.ref)
                        (f := fun entry : GroupNode => entry.group.node.ref)).symm
                    rw [mapped]
                    exact currentUnique.filter _
                  have nextPresent : ∀ ref ∈ kept.map Execution.DeliveryNode.ref,
                      ∃ entry ∈ next.groupNodes,
                        entry.group.node.ref = ref
                          ∧ (entry.tasks.isEmpty && entry.failure.isNone) ≠ true := by
                    intro ref member
                    obtain ⟨entry, entryMember, same, positive⟩ :=
                      keptPresent ref member
                    have different : entry.group.node.ref ≠ group.ref := by
                      intro equal
                      have sameNode : entry = node :=
                        currentUnique.sameNode entryMember
                          (List.mem_of_find?_eq_some found)
                          (equal.trans (current.groupNode?_ref found).symm)
                      subst entry
                      exact positive zero
                    refine ⟨entry, ?_, same, positive⟩
                    exact List.mem_filter.mpr
                      ⟨entryMember, by simp [bne, different]⟩
                  exact ih _ _ _ nextUnique nextPresent
                · simp only [zero]
                  have nextPresent :
                      ∀ ref ∈ (kept ++ [group]).map Execution.DeliveryNode.ref,
                        ∃ entry ∈ current.groupNodes,
                          entry.group.node.ref = ref
                            ∧ (entry.tasks.isEmpty && entry.failure.isNone) ≠ true := by
                    intro ref member
                    rw [List.map_append, List.mem_append] at member
                    rcases member with old | added
                    · exact keptPresent ref old
                    · have equal : ref = group.ref := by simpa using added
                      subst ref
                      exact ⟨node, List.mem_of_find?_eq_some found,
                        current.groupNode?_ref found, zero⟩
                  exact ih _ _ _ currentUnique nextPresent
  have empty : ∀ ref ∈ ([] : List Execution.DeliveryNode).map
      Execution.DeliveryNode.ref,
      ∃ node ∈ queue.groupNodes,
        node.group.node.ref = ref ∧ (node.tasks.isEmpty && node.failure.isNone) ≠ true := by
    intro ref member
    cases member
  exact loop _ queue groups [] unique empty

/-- Every nonempty group retained by pruning still has a live group node.
Witness: project ref presence from the stronger post-pruning contents certificate.
The result records input descriptors, so only ref presence is asserted here.
-/
theorem State.pruneEmptyGroups_keptPresent
    (queue : State) (groups : List Execution.DeliveryNode)
    (unique : queue.GroupRefsUnique)
    : ∀ ref ∈ (queue.pruneEmptyGroups groups).2.map Execution.DeliveryNode.ref,
        ref
        ∈ (queue.pruneEmptyGroups groups).1.groupNodes.map
            (fun node => node.group.node.ref) := by
  intro ref member
  obtain ⟨node, present, same, _⟩ := queue.pruneEmptyGroups_keptContents groups unique ref member
  exact List.mem_map.mpr ⟨node, present, same⟩

/-- Activating root tasks and streams does not modify the group-node map. -/
theorem State.GroupRefsUnique.startNewWork {queue : State}
    (unique : queue.GroupRefsUnique) (newWork : NewWork)
    : (queue.startNewWork newWork).GroupRefsUnique := by
  let groups := newWork.newGroups.map Execution.DeliveryNode.ref
  let streams := newWork.newStreams.map Execution.DeliveryNode.ref
  let current : State := { queue with rootGroups := queue.rootGroups ++ groups }
  have groupFold (refs : NodeRefs) :
      ∀ current, current.GroupRefsUnique →
        (refs.foldl State.startGroup current).GroupRefsUnique := by
    induction refs with
    | nil => intro current currentUnique; exact currentUnique
    | cons ref rest ih =>
        intro current currentUnique
        apply ih (current.startGroup ref)
        unfold State.startGroup
        split
        · exact currentUnique
        · rename_i node found
          have taskFold (tasks : List Occurrence) :
              ∀ current, current.GroupRefsUnique →
                (tasks.foldl State.startTask current).GroupRefsUnique := by
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
  have streamFold (refs : NodeRefs) :
      ∀ current, current.GroupRefsUnique →
        (refs.foldl State.startStream current).GroupRefsUnique := by
    induction refs with
    | nil => intro current currentUnique; exact currentUnique
    | cons ref rest ih =>
        intro current currentUnique
        apply ih (current.startStream ref)
        unfold State.startStream
        split <;> exact currentUnique
  change (streams.foldl State.startStream
    (groups.foldl State.startGroup current)).GroupRefsUnique
  exact streamFold streams _ (groupFold groups current unique)

/-- Queue initialization has at most one live group node per delivery ref. -/
theorem createWorkQueue_groupRefsUnique (work : Work)
    : (State.initialize work).GroupRefsUnique := by
  let integrated := (({} : State).maybeIntegrateWork work).1
  let newWork := (({} : State).maybeIntegrateWork work).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  let started := pruned.startNewWork roots
  have emptyUnique : ({} : State).GroupRefsUnique := by simp [State.GroupRefsUnique]
  have integratedUnique : integrated.GroupRefsUnique :=
    emptyUnique.maybeIntegrateWork work
  have prunedUnique : pruned.GroupRefsUnique :=
    integratedUnique.pruneEmptyGroups newWork.newGroups
  have startedUnique : started.GroupRefsUnique := prunedUnique.startNewWork roots
  change State.GroupRefsUnique
    { started with initialGroups := groups, initialStreams := roots.newStreams }
  exact startedUnique

/-- Filtering the group-node map can only remove ref occurrences. -/
theorem State.GroupRefsUnique.filterGroupNodes {queue : State}
    (unique : queue.GroupRefsUnique) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep }).GroupRefsUnique := by
  change ((queue.groupNodes.filter keep).map
    (fun node => node.group.node.ref)).Nodup
  exact List.Nodup.sublist ((List.filter_sublist).map _) unique

/-- Flushing a task removes memberships but keeps the group-ref list. -/
theorem State.GroupRefsUnique.removeTask {queue : State}
    (unique : queue.GroupRefsUnique) (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupRefsUnique := by
  change ((queue.groupNodes.map
    (fun node => { node with tasks := node.tasks.filter (· != occurrence) })).map
      (fun node => node.group.node.ref)).Nodup
  simpa [List.map_map, Function.comp_def, State.GroupRefsUnique] using unique

/-- Cancelling a group and its descendants retains a filtered ref subset. -/
theorem State.GroupRefsUnique.removeGroup {queue : State}
    (unique : queue.GroupRefsUnique) (ref : NodeRef)
    : (queue.removeGroup ref).GroupRefsUnique := by
  unfold State.removeGroup
  exact unique.filterGroupNodes _

/-- Flushing a successful group preserves unique refs while removing shared
memberships, its own node, and possibly empty descendants.
-/
theorem State.GroupRefsUnique.finishGroupSuccess {queue : State}
    (unique : queue.GroupRefsUnique) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupRefsUnique := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs)
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
  have stepUnique (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence) (currentUnique : acc.1.GroupRefsUnique)
      : (step acc occurrence).1.GroupRefsUnique := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentUnique
    · exact currentUnique.removeTask occurrence
  have foldUnique (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.GroupRefsUnique → (tasks.foldl step acc).1.GroupRefsUnique := by
    induction tasks with
    | nil => intro acc currentUnique; exact currentUnique
    | cons occurrence rest ih =>
        intro acc currentUnique
        exact ih (step acc occurrence) (stepUnique acc occurrence currentUnique)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedUnique : flushed.GroupRefsUnique :=
    foldUnique group.tasks (queue, [], []) unique
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentUnique : current.GroupRefsUnique :=
    flushedUnique.filterGroupNodes _
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.GroupRefsUnique
  exact currentUnique.pruneEmptyGroups children

/-- Every group ref released by a successful group flush still has a live
node after empty-child pruning. -/
theorem State.finishGroupSuccess_newGroupsPresent
    {queue : State} (unique : queue.GroupRefsUnique) (group : GroupNode)
    : ∀ ref ∈
        (queue.finishGroupSuccess group).2.2.newGroups.map Execution.DeliveryNode.ref,
        ref
        ∈ (queue.finishGroupSuccess group).1.groupNodes.map
            (fun node => node.group.node.ref) := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs)
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
  have stepUnique (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence) (currentUnique : acc.1.GroupRefsUnique)
      : (step acc occurrence).1.GroupRefsUnique := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact currentUnique
    · exact currentUnique.removeTask occurrence
  have foldUnique (tasks : List Occurrence) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.GroupRefsUnique → (tasks.foldl step acc).1.GroupRefsUnique := by
    induction tasks with
    | nil => intro acc currentUnique; exact currentUnique
    | cons occurrence rest ih =>
        intro acc currentUnique
        exact ih (step acc occurrence) (stepUnique acc occurrence currentUnique)
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedUnique : flushed.GroupRefsUnique :=
    foldUnique group.tasks (queue, [], []) unique
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentUnique : current.GroupRefsUnique :=
    flushedUnique.filterGroupNodes _
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change ∀ ref ∈ (current.pruneEmptyGroups children).2.map
      Execution.DeliveryNode.ref,
      ref ∈ (current.pruneEmptyGroups children).1.groupNodes.map
        (fun node => node.group.node.ref)
  exact current.pruneEmptyGroups_keptPresent children currentUnique

/-- Failing a group retains only a filtered subset of live group refs. -/
theorem State.GroupRefsUnique.finishGroupFailure {queue : State}
    (unique : queue.GroupRefsUnique) (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.GroupRefsUnique :=
  unique.removeGroup group.group.node.ref

/-- Draining ready groups cannot duplicate a live ref.
Witness: induction over the drain bound, using closure and activation preservation.
-/
theorem State.GroupRefsUnique.drainReadyGroups {queue : State}
    (unique : queue.GroupRefsUnique)
    : queue.drainReadyGroups.1.GroupRefsUnique := by
  have loop (fuel : Nat) (current : State) (unique : current.GroupRefsUnique)
      : (State.drainReadyGroups.go fuel current).1.GroupRefsUnique := by
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

/-- A failed task closes active owners or retains latent errors without duplicating refs.
Witness: task removal and each owner update preserve ref uniqueness.
-/
theorem State.GroupRefsUnique.taskFailure {queue : State}
    (unique : queue.GroupRefsUnique) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.GroupRefsUnique := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent :=
    let (current, events) := acc
    match current.groupNode? group.ref with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.ref then
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
      (currentUnique : acc.1.GroupRefsUnique)
      : (step acc group).1.GroupRefsUnique := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    cases found : current.groupNode? group.ref with
    | none => exact currentUnique
    | some node =>
        by_cases started : current.rootGroups.contains group.ref = true
        · simp only [started, ite_true]
          exact currentUnique.finishGroupFailure node errors
        · simp only [started]
          exact currentUnique.putGroupNode _
  have foldUnique (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupRefsUnique → (groups.foldl step acc).1.GroupRefsUnique := by
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
    have currentUnique : current.GroupRefsUnique := unique.removeTask occurrence
    change (taskNode.task.groups.foldl step (current, [])).1.GroupRefsUnique
    exact foldUnique taskNode.task.groups (current, []) currentUnique

/-- Successful stream-item integration preserves unique group refs. -/
theorem State.GroupRefsUnique.streamItems {queue : State}
    (unique : queue.GroupRefsUnique) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.GroupRefsUnique := by
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
      (item : StreamItem) (currentUnique : acc.1.GroupRefsUnique)
      : (step acc item).1.GroupRefsUnique := by
    obtain ⟨current, groups, streams, values⟩ := acc
    let integrated := current.maybeIntegrateWork item.work
    have integratedUnique : integrated.1.GroupRefsUnique :=
      currentUnique.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have prunedUnique : pruned.1.GroupRefsUnique :=
      integratedUnique.pruneEmptyGroups integrated.2.newGroups
    exact prunedUnique.startNewWork { integrated.2 with newGroups := pruned.2 }
  have foldUnique (more : List StreamItem) :
      ∀ acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue,
        acc.1.GroupRefsUnique → (more.foldl step acc).1.GroupRefsUnique := by
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
theorem State.GroupRefsUnique.streamSuccess {queue : State}
    (unique : queue.GroupRefsUnique) (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.GroupRefsUnique := by
  unfold State.streamSuccess
  split <;> exact unique

/-- Failed stream closure does not touch the group-node map either. -/
theorem State.GroupRefsUnique.streamFailure {queue : State}
    (unique : queue.GroupRefsUnique) (stream : Execution.DeliveryNode)
    (errors : Nat)
    : (queue.streamFailure stream errors).1.GroupRefsUnique := by
  unfold State.streamFailure
  split <;> exact unique

/-- Task success integrates child work, updates contributor counters, and may
flush completed groups; each stage preserves unique live group refs.
-/
theorem State.GroupRefsUnique.taskSuccess {queue : State}
    (unique : queue.GroupRefsUnique) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.GroupRefsUnique := by
  let settleStep (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have settleUnique (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.GroupRefsUnique)
      : (settleStep current group).GroupRefsUnique := by
    unfold settleStep
    split
    · exact currentUnique
    · exact currentUnique.putGroupNode _
  let releaseStep (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent × NewWork :=
    let (current, events, released) := acc
    match current.groupNode? group.ref with
    | none => (current, events, released)
    | some node =>
        let node := { node with pending := node.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.ref && node.pending == 0
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
      (group : Execution.DeliveryNode) (currentUnique : acc.1.GroupRefsUnique)
      : (releaseStep acc group).1.GroupRefsUnique := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [releaseStep]
    split
    · exact currentUnique
    · rename_i node found
      have decremented : (current.putGroupNode
          { node with pending := node.pending - 1 }).GroupRefsUnique := by
        simpa only [settleStep, found] using settleUnique current group currentUnique
      split
      · exact decremented.finishGroupSuccess _
      · exact decremented
  have releaseFold (groups : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.GroupRefsUnique → (groups.foldl releaseStep acc).1.GroupRefsUnique := by
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
    have withValueUnique : withValue.GroupRefsUnique := unique
    let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
    have integratedUnique : integrated.GroupRefsUnique :=
      withValueUnique.maybeIntegrateWork result.work (some occurrence)
    let finished := taskNode.task.groups.foldl releaseStep (integrated, [], {})
    have finishedUnique : finished.1.GroupRefsUnique :=
      releaseFold taskNode.task.groups (integrated, [], {}) integratedUnique
    change (finished.1.startNewWork finished.2.2).drainReadyGroups.1.GroupRefsUnique
    exact (finishedUnique.startNewWork finished.2.2).drainReadyGroups

/-- Every individual host event preserves unique live group refs. -/
theorem State.GroupRefsUnique.handleGraphEvent {queue : State}
    (unique : queue.GroupRefsUnique) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.GroupRefsUnique := by
  cases event with
  | taskSuccess occurrence result => exact unique.taskSuccess occurrence result
  | taskFailure occurrence errors => exact unique.taskFailure occurrence errors
  | streamItems stream items => exact unique.streamItems stream items
  | streamSuccess stream => exact unique.streamSuccess stream
  | streamFailure stream errors => exact unique.streamFailure stream errors

/-- Every available host batch preserves unique live group refs. -/
theorem State.GroupRefsUnique.handleGraphEvents {queue : State}
    (unique : queue.GroupRefsUnique) (batch : List GraphEvent)
    : (queue.handleGraphEvents batch).1.GroupRefsUnique := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have foldUnique (events : List GraphEvent) :
      ∀ acc : State × List WorkQueueEvent,
        acc.1.GroupRefsUnique → (events.foldl step acc).1.GroupRefsUnique := by
    induction events with
    | nil => intro acc currentUnique; exact currentUnique
    | cons event rest ih =>
        intro acc currentUnique
        obtain ⟨current, outputs⟩ := acc
        have nextUnique : (step (current, outputs) event).1.GroupRefsUnique :=
          currentUnique.handleGraphEvent event
        exact ih (step (current, outputs) event) nextUnique
  unfold State.handleGraphEvents
  split
  · exact unique
  · cases outcome : batch.foldl step (queue, []) with
    | mk current outputs =>
        have currentUnique : current.GroupRefsUnique := by
          have folded := foldUnique batch (queue, []) unique
          rw [outcome] at folded
          exact folded
        dsimp only
        split <;> exact currentUnique

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
