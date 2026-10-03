import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants

/-! Successful promotion follows stored live child paths, including pruned empty shells. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful settlement removes nodes but does not invent child edges
-----------------------------------------------------------------------------------------

/-- Every live lookup in `after` retains a node's child list from `before`.
This proof-side relation compares existing queue records; it allocates no work graph. -/
def State.GroupEdgesFrom (after before : State) : Prop :=
  ∀ ref node,
    after.groupNode? ref = some node
    → ∃ old, before.groupNode? ref = some old ∧ node.childGroups = old.childGroups

/-- An unchanged queue retains its own edges. Witness: reuse each lookup. -/
theorem State.GroupEdgesFrom.refl (queue : State) : queue.GroupEdgesFrom queue := by
  intro ref node found
  exact ⟨node, found, rfl⟩

/-- Edge provenance composes through successive queue states.
Witness: compose the lookup witnesses and child-list equalities. -/
theorem State.GroupEdgesFrom.trans {first middle last : State}
    (later : last.GroupEdgesFrom middle) (earlier : middle.GroupEdgesFrom first)
    : last.GroupEdgesFrom first := by
  intro ref node found
  obtain ⟨mid, midFound, midChildren⟩ := later ref node found
  obtain ⟨old, oldFound, oldChildren⟩ := earlier ref mid midFound
  exact ⟨old, oldFound, midChildren.trans oldChildren⟩

/-- A live path in the later queue already existed in the earlier queue.
Witness: induction on the path, transporting every lookup and child-list membership. -/
theorem State.GroupEdgesFrom.liveDescendant {before after : State}
    (edges : after.GroupEdgesFrom before) {root target}
    (path : after.LiveDescendant root target)
    : before.LiveDescendant root target := by
  induction path with
  | self found =>
      obtain ⟨old, oldFound, _⟩ := edges _ _ found
      exact .self oldFound
  | child found linked below ih =>
      obtain ⟨old, oldFound, children⟩ := edges _ _ found
      exact .child oldFound (children ▸ linked) ih

/-- A ref-preserving node map that retains child lists preserves edge provenance.
Witness: a mapped lookup comes from the same earlier ref and its mapped node. -/
private theorem State.groupEdgesFrom_map (queue : State) (update : GroupNode → GroupNode)
    (sameRef : ∀ node, (update node).group.node.ref = node.group.node.ref)
    (sameChildren
      : ∀ node ∈ queue.groupNodes, (update node).childGroups = node.childGroups)
    : ({ queue with groupNodes := queue.groupNodes.map update }).GroupEdgesFrom
        queue := by
  intro ref node found
  have lookup : ({ queue with groupNodes := queue.groupNodes.map update }).groupNode? ref
      = (queue.groupNode? ref).map update := by
    simp only [State.groupNode?, List.find?_map, Function.comp_def, sameRef]
  rw [lookup] at found
  cases oldFound : queue.groupNode? ref with
  | none => simp [oldFound] at found
  | some old =>
      have same : update old = node := by simpa [oldFound] using found
      exact ⟨old, rfl, same ▸ sameChildren old (List.mem_of_find?_eq_some oldFound)⟩

/-- Dropping a task changes memberships, not stored child links.
Witness: its group-node update preserves refs and child lists pointwise. -/
theorem State.removeTask_groupEdgesFrom (queue : State) (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupEdgesFrom queue :=
  queue.groupEdgesFrom_map
    (fun node => { node with tasks := node.tasks.filter (· != occurrence) })
    (fun _ => rfl) (fun _ _ => rfl)

/-- Filtering live nodes by ref retains every surviving lookup and child list.
Witness: the ref-filter lookup equation; missing nodes produce no new edges. -/
theorem State.filterRefs_groupEdgesFrom (queue : State) (keep : Nat → Bool)
    : ({
        queue with
          groupNodes :=
            queue.groupNodes.filter (fun node => keep node.group.node.ref)
      }).GroupEdgesFrom
        queue := by
  intro ref node found
  change (queue.groupNodes.filter (fun node => keep node.group.node.ref)).find?
    (fun node => node.group.node.ref == ref) = some node at found
  rw [queue.groupNode?_filterRefs keep ref] at found
  split at found
  · exact ⟨node, found, rfl⟩
  · contradiction

/-- Updating the looked-up group's pending counter preserves all live edges.
Witness: unique refs identify every replaced entry with the original looked-up node. -/
theorem State.putPending_groupEdgesFrom {queue : State} (unique : queue.GroupRefsUnique)
    {ref : NodeRef} {node : GroupNode} (found : queue.groupNode? ref = some node)
    (pending : Nat)
    : (queue.putGroupNode { node with pending }).GroupEdgesFrom queue := by
  apply queue.groupEdgesFrom_map
    (fun old => if old.group.node.ref == node.group.node.ref then { node with pending } else old)
  · intro old
    split
    · rename_i equal
      exact (beq_iff_eq.mp equal).symm
    · rfl
  · intro old member
    split
    · rename_i equal
      have same := unique.sameNode member (List.mem_of_find?_eq_some found)
        (beq_iff_eq.mp equal)
      change node.childGroups = old.childGroups
      exact congrArg GroupNode.childGroups same.symm
    · rfl

-----------------------------------------------------------------------------------------
-- Pruning only promotes descendants of the original candidate roots
-----------------------------------------------------------------------------------------

/-- Every group retained by pruning descends from an original candidate in the input
queue; all surviving child edges also come from that queue. Witness: fuel induction
tracking candidate paths before each removal, including skipped stale child refs.
No acyclicity, task-accounting, or health assumption is required. -/
theorem State.pruneEmptyGroups_descendants (queue : State)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupEdgesFrom queue
      ∧ ∀ node ∈ (queue.pruneEmptyGroups groups).2,
          ∃ root ∈ groups, queue.LiveDescendant root.ref node.ref := by
  let reachable (ref : NodeRef) := ∃ root ∈ groups, queue.LiveDescendant root.ref ref
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (edges : current.GroupEdgesFrom queue)
      (pending : ∀ group ∈ remaining, ∀ node,
        current.groupNode? group.ref = some node → reachable group.ref)
      (done : ∀ group ∈ kept, reachable group.ref)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupEdgesFrom queue
        ∧ ∀ node ∈ (State.pruneEmptyGroups.go fuel current remaining kept).2,
            reachable node.ref := by
    induction fuel generalizing current remaining kept with
    | zero => exact ⟨edges, done⟩
    | succ fuel ih =>
        cases remaining with
        | nil => exact ⟨edges, done⟩
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih current rest kept edges
                (fun candidate member => pending candidate (List.mem_cons_of_mem _ member)) done
            · rename_i node found
              have reached := pending group List.mem_cons_self node found
              split
              · let next : State :=
                  { current with groupNodes :=
                    current.groupNodes.filter (fun entry => entry.group.node.ref != group.ref) }
                have retained : next.GroupEdgesFrom current :=
                  current.filterRefs_groupEdgesFrom (· != group.ref)
                apply ih next _ kept (retained.trans edges) _ done
                intro candidate member later laterFound
                rcases List.mem_append.mp member with child | tail
                · obtain ⟨ref, linked, selected⟩ := List.mem_filterMap.mp child
                  cases childFound : current.groupNode? ref with
                  | none => simp [childFound] at selected
                  | some childNode =>
                      have same : childNode.group.node = candidate := by
                        simpa [childFound] using selected
                      obtain ⟨root, rootMember, path⟩ := reached
                      have childPath : current.LiveDescendant group.ref ref :=
                        .child found linked (.self childFound)
                      have childRef : ref = candidate.ref :=
                        (State.groupNode?_ref childFound).symm.trans (congrArg _ same)
                      exact ⟨root, rootMember, childRef ▸ path.trans
                        (edges.liveDescendant childPath)⟩
                · obtain ⟨old, oldFound, _⟩ := retained candidate.ref later laterFound
                  exact pending candidate (List.mem_cons_of_mem _ tail) old oldFound
              · apply ih current rest (kept ++ [group]) edges
                  (fun candidate member => pending candidate (List.mem_cons_of_mem _ member))
                intro candidate member
                rcases List.mem_append.mp member with earlier | latest
                · exact done candidate earlier
                · have same := List.mem_singleton.mp latest
                  exact same ▸ reached
  exact loop _ queue groups [] (State.GroupEdgesFrom.refl queue)
    (fun group member node found => ⟨group, member, .self found⟩)
    (by intro group member; cases member)

-----------------------------------------------------------------------------------------
-- Group completion releases only descendants of its stored children
-----------------------------------------------------------------------------------------

/-- Group completion retains old edges and promotes only nodes below its supplied child
refs. Witness: flushing preserves child lists, closure filters the completed node, and
pruning retains paths through any removed empty shells. No health or accounting premise.
-/
theorem State.finishGroupSuccess_descendants (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupEdgesFrom queue
      ∧ ∀ node ∈ (queue.finishGroupSuccess group).2.2.newGroups,
          ∃ child ∈ group.childGroups, queue.LiveDescendant child node.ref := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have loop (more : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (edges : acc.1.GroupEdgesFrom queue)
      : (more.foldl step acc).1.GroupEdgesFrom queue := by
    induction more generalizing acc with
    | nil => exact edges
    | cons occurrence rest ih =>
        apply ih (step acc occurrence)
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact edges
        · exact (current.removeTask_groupEdgesFrom occurrence).trans edges
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedEdges : flushed.GroupEdgesFrom queue :=
    loop group.tasks (queue, [], []) (State.GroupEdgesFrom.refl queue)
  let current : State :=
    {
      flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref)
    }
  have currentEdges : current.GroupEdgesFrom queue :=
    (flushed.filterRefs_groupEdgesFrom (· != group.group.node.ref)).trans flushedEdges
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  have pruned := current.pruneEmptyGroups_descendants children
  refine ⟨pruned.1.trans currentEdges, ?_⟩
  intro node released
  obtain ⟨child, candidate, path⟩ := pruned.2 node released
  obtain ⟨ref, linked, selected⟩ := List.mem_filterMap.mp candidate
  cases found : current.groupNode? ref with
  | none => simp [found] at selected
  | some childNode =>
      have same : childNode.group.node = child := by simpa [found] using selected
      have childRef : child.ref = ref :=
        (congrArg Execution.DeliveryNode.ref same).symm.trans (State.groupNode?_ref found)
      exact ⟨ref, linked, childRef ▸ currentEdges.liveDescendant path⟩

/-- Completing an actual live node releases only its earlier live descendants.
Witness: prepend its successful lookup and stored child edge to each pruning path. -/
theorem State.finishGroupSuccess_released_descendant {queue : State} {group : GroupNode}
    (found : queue.groupNode? group.group.node.ref = some group)
    {node : Execution.DeliveryNode}
    (released : node ∈ (queue.finishGroupSuccess group).2.2.newGroups)
    : queue.LiveDescendant group.group.node.ref node.ref := by
  obtain ⟨child, linked, path⟩ := (queue.finishGroupSuccess_descendants group).2 node released
  exact .child found linked path

-----------------------------------------------------------------------------------------
-- The release-time drain stays within its original active subtrees
-----------------------------------------------------------------------------------------

/-- Draining ready groups retains old child edges and promotes only descendants of
earlier active roots. Witness: closure/activation induction carries paths back through
each successful release; failure only removes records and roots. -/
theorem State.drainReadyGroups_descendants (queue : State)
    (unique : queue.GroupRefsUnique)
    : queue.drainReadyGroups.1.GroupEdgesFrom queue
      ∧ ∀ ref ∈ queue.drainReadyGroups.1.rootGroups,
          ref ∈ queue.rootGroups
          ∨ ∃ root ∈ queue.rootGroups, queue.LiveDescendant root ref := by
  let invariant (current : State) := current.GroupRefsUnique
    ∧ current.GroupEdgesFrom queue
    ∧ ∀ ref ∈ current.rootGroups,
        ref ∈ queue.rootGroups
        ∨ ∃ root ∈ queue.rootGroups, queue.LiveDescendant root ref
  have result := State.drainReadyGroups_preserves invariant
    (fun current node prior member active _ _ => by
      have found := prior.1.groupNode?_of_mem member
      have completed := current.finishGroupSuccess_descendants node
      have refs := (prior.1.finishGroupSuccess node).startNewWork
        (current.finishGroupSuccess node).2.2
      have edges : ((current.finishGroupSuccess node).1.startNewWork
          (current.finishGroupSuccess node).2.2).GroupEdgesFrom current := by
        intro ref child found
        rw [State.groupNode?, (State.startNewWork_groupCore _ _).1] at found
        exact completed.1 ref child found
      refine ⟨refs, edges.trans prior.2.1, ?_⟩
      intro ref rootMember
      rw [(State.startNewWork_groupCore _ _).2.2] at rootMember
      rcases List.mem_append.mp rootMember with old | released
      · exact prior.2.2 ref (current.finishGroupSuccess_rootsSubset node old)
      · obtain ⟨child, released, sameRef⟩ := List.mem_map.mp released
        have path : queue.LiveDescendant node.group.node.ref ref :=
          sameRef ▸ prior.2.1.liveDescendant
            (State.finishGroupSuccess_released_descendant found released)
        rcases prior.2.2 node.group.node.ref active with root | ⟨root, rootMember, earlier⟩
        · exact Or.inr ⟨node.group.node.ref, root, path⟩
        · exact Or.inr ⟨root, rootMember, earlier.trans path⟩)
    (fun current node errors prior _ _ _ => by
      have edges : (current.finishGroupFailure node errors).1.GroupEdgesFrom current :=
        current.filterRefs_groupEdgesFrom (fun ref =>
          !(State.removeGroup.collect (current.groupNodes.length + 1) current
            [node.group.node.ref] []).contains ref)
      exact ⟨prior.1.finishGroupFailure node errors, edges.trans prior.2.1,
        fun ref member => prior.2.2 ref
          (current.removeGroup_rootsSubset node.group.node.ref member)⟩)
    (show invariant queue from
      ⟨unique, State.GroupEdgesFrom.refl queue, fun _ member => Or.inl member⟩)
  exact result.2

-----------------------------------------------------------------------------------------
-- The single-pass success loop never promotes outside the old active subtrees
-----------------------------------------------------------------------------------------

/-- Every root released by the contributor loop descends from a root active before that
loop. Witness: retain edge provenance and root-subset facts through every decrement and
flush, while accumulating paths for released groups before later removals can hide them.
Contributor order and overlapping ancestor/descendant owners are unrestricted. -/
private theorem successGroupFold_shape (queue : State) (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    : let final := groups.foldl successGroupStep (queue, [], {})
      final.1.GroupRefsUnique
      ∧ final.1.GroupEdgesFrom queue
      ∧ final.1.rootGroups.Subset queue.rootGroups
      ∧ ∀ node ∈ final.2.2.newGroups,
          ∃ root ∈ queue.rootGroups, queue.LiveDescendant root node.ref := by
  let property (acc : State × List WorkQueueEvent × NewWork) := acc.1.GroupRefsUnique
    ∧ acc.1.GroupEdgesFrom queue ∧ acc.1.rootGroups.Subset queue.rootGroups
    ∧ ∀ node ∈ acc.2.2.newGroups,
        ∃ root ∈ queue.rootGroups, queue.LiveDescendant root node.ref
  have stepPreserves (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) (prior : property acc)
      : property (successGroupStep acc group) := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact prior
    · rename_i node found
      let updated := current.putGroupNode { node with pending := node.pending - 1 }
      have updatedEdges : updated.GroupEdgesFrom current :=
        State.putPending_groupEdgesFrom prior.1 found _
      have updatedRefs : updated.GroupRefsUnique := prior.1.putGroupNode _
      split
      · rename_i finishes
        have active : group.ref ∈ current.rootGroups := by
          have flags := Bool.and_eq_true_iff.mp finishes
          simpa [State.putGroupNode] using (Bool.and_eq_true_iff.mp flags.1).1
        have completed := updated.finishGroupSuccess_descendants
          { node with pending := node.pending - 1 }
        refine ⟨updatedRefs.finishGroupSuccess _,
          completed.1.trans (updatedEdges.trans prior.2.1), ?_, ?_⟩
        · intro ref member
          exact prior.2.2.1
            (updated.finishGroupSuccess_rootsSubset { node with pending := node.pending - 1 }
              member)
        · intro next member
          rcases List.mem_append.mp member with earlier | latest
          · exact prior.2.2.2 next earlier
          · obtain ⟨child, linked, path⟩ := completed.2 next latest
            have currentPath : current.LiveDescendant group.ref next.ref :=
              .child found linked (updatedEdges.liveDescendant path)
            exact ⟨group.ref, prior.2.2.1 active, prior.2.1.liveDescendant currentPath⟩
      · exact ⟨updatedRefs, updatedEdges.trans prior.2.1, prior.2.2⟩
  have loop (more : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork) (prior : property acc)
      : property (more.foldl successGroupStep acc) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons group rest ih => exact ih _ (stepPreserves acc group prior)
  exact loop groups (queue, [], {})
    ⟨
      unique,
      State.GroupEdgesFrom.refl queue,
      fun _ member => member,
      by intro node member; cases member
    ⟩

/-- The single-pass contributor loop retains old edges and releases only descendants
of its original active roots. Witness: project the joint unique-ref/path invariant. -/
theorem successGroupFold_descendants (queue : State) (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    : let final := groups.foldl successGroupStep (queue, [], {})
      final.1.GroupEdgesFrom queue
      ∧ final.1.rootGroups.Subset queue.rootGroups
      ∧ ∀ node ∈ final.2.2.newGroups,
          ∃ root ∈ queue.rootGroups, queue.LiveDescendant root node.ref :=
  (successGroupFold_shape queue unique groups).2

/-- The contributor fold retains unique live group refs.
Witness: project the same joint shape invariant used for edge and release provenance.
-/
theorem successGroupFold_groupRefsUnique (queue : State) (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).1.GroupRefsUnique :=
  (successGroupFold_shape queue unique groups).1

/-- Every surviving successful-handler record comes from child integration unchanged in shape.
Witness: compose edge provenance through the single-pass fold, activation, and final drain.
This supplies pre-release survival without assuming the resulting events are admitted.
-/
theorem State.taskSuccess_integration_groupEdgesFrom {queue : State}
    (unique : queue.GroupRefsUnique) {occurrence result taskNode}
    (found : queue.taskNode? occurrence = some taskNode)
    (healthy : queue.taskHasHealthyOwner taskNode.task = true)
    : let integrated :=
        ((queue.putTaskNode
            { taskNode with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      (queue.taskSuccess occurrence result).1.GroupEdgesFrom integrated := by
  intro integrated
  have storedRefs : (queue.putTaskNode
      { taskNode with value := some result.value }).GroupRefsUnique := unique
  have integratedRefs := storedRefs.maybeIntegrateWork result.work (some occurrence)
  let folded := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
  let active := folded.1.startNewWork folded.2.2
  have edges : active.GroupEdgesFrom integrated := by
    intro ref node lookup
    rw [State.groupNode?, (State.startNewWork_groupCore _ _).1] at lookup
    exact (successGroupFold_descendants integrated integratedRefs taskNode.task.groups).1
      ref node lookup
  have activeRefs := (successGroupFold_groupRefsUnique integrated integratedRefs
    taskNode.task.groups).startNewWork folded.2.2
  rw [queue.taskSuccess_eq occurrence result taskNode found]
  simp only [healthy, Bool.not_true, Bool.false_eq_true, ite_false]
  exact (active.drainReadyGroups_descendants activeRefs).1.trans edges

/-- A task-success handler adds only roots reachable from its earlier active roots in
the post-integration queue. Witness: the single-pass fold, activation, and final drain
retain ancestor paths. Ignored settlements add no roots. Integration, not promotion,
is where new edges still require a generated-work health argument. -/
theorem State.taskSuccess_rootOrigins {queue : State} (unique : queue.GroupRefsUnique)
    (occurrence : Occurrence) (result : TaskResult) (taskNode : TaskNode)
    (found : queue.taskNode? occurrence = some taskNode)
    : let integrated :=
        ((queue.putTaskNode
            { taskNode with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      ∀ ref ∈ (queue.taskSuccess occurrence result).1.rootGroups,
        ref ∈ queue.rootGroups
        ∨ ∃ root ∈ queue.rootGroups, integrated.LiveDescendant root ref := by
  let stored := queue.putTaskNode { taskNode with value := some result.value }
  let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
  have storedRefs : stored.GroupRefsUnique := unique
  have shape := successGroupFold_shape integrated
    (storedRefs.maybeIntegrateWork result.work (some occurrence)) taskNode.task.groups
  have facts := shape.2
  have roots : integrated.rootGroups = queue.rootGroups :=
    stored.maybeIntegrateWork_rootGroups result.work (some occurrence)
  dsimp only
  intro ref active
  rw [queue.taskSuccess_eq occurrence result taskNode found] at active
  split at active
  · exact Or.inl active
  · rename_i accepted
    let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
    let activated := released.1.startNewWork released.2.2
    have edges : activated.GroupEdgesFrom integrated := by
      intro ref node found
      rw [State.groupNode?, (State.startNewWork_groupCore _ _).1] at found
      exact facts.1 ref node found
    have origins : ∀ ref ∈ activated.rootGroups,
        ref ∈ queue.rootGroups
        ∨ ∃ root ∈ queue.rootGroups, integrated.LiveDescendant root ref := by
      intro ref active
      rw [(released.1.startNewWork_groupCore released.2.2).2.2] at active
      rcases List.mem_append.mp active with old | new
      · exact .inl (roots ▸ facts.2.1 old)
      · obtain ⟨node, member, sameRef⟩ := List.mem_map.mp new
        obtain ⟨root, rootMember, path⟩ := facts.2.2 node member
        exact .inr ⟨root, roots ▸ rootMember, sameRef ▸ path⟩
    change ref ∈ activated.drainReadyGroups.1.rootGroups at active
    have drained := activated.drainReadyGroups_descendants (shape.1.startNewWork released.2.2)
    rcases drained.2 ref active with old | ⟨root, rootMember, path⟩
    · exact origins ref old
    · have path := edges.liveDescendant path
      rcases origins root rootMember with old | ⟨ancestor, ancestorMember, earlier⟩
      · exact Or.inr ⟨root, old, path⟩
      · exact Or.inr ⟨ancestor, ancestorMember, earlier.trans path⟩

/-- Healthy old roots and healthy post-integration root subtrees suffice for task-success
root health. Witness: the structural root-origin theorem, not assumed output admission.
Establishing the subtree hypothesis from source replay remains a separate obligation. -/
theorem State.RootGroupsHealthy.taskSuccess_of_descendants {queue : State} {work failed}
    (healthy : queue.RootGroupsHealthy work failed) (unique : queue.GroupRefsUnique)
    (occurrence : Occurrence) (result : TaskResult) (taskNode : TaskNode)
    (found : queue.taskNode? occurrence = some taskNode)
    (descendants
      : let integrated :=
          ((queue.putTaskNode
              { taskNode with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1
        ∀ root ∈ queue.rootGroups,
          ∀ ref, integrated.LiveDescendant root ref → ¬GroupInvalidated work failed ref)
    : (queue.taskSuccess occurrence result).1.RootGroupsHealthy work failed := by
  intro ref active
  rcases queue.taskSuccess_rootOrigins unique occurrence result taskNode found ref active
      with old | ⟨root, member, path⟩
  · exact healthy ref old
  · exact descendants root member ref path

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
