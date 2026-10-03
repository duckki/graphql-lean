import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationCandidates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation

/-! Integration and initialization preserve healthy retired-ancestor certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Integration creates only cancelled retirements; healthy retirement is inherited
-----------------------------------------------------------------------------------------

/-- A preserved predicate extends through the actual state fold.
Witness: induction on its inputs, without replacing any intermediate queue. -/
private theorem fold_preserves {α β : Type} (step : β → α → β) (property : β → Prop)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List α) (state : β) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih _ (preserved state item initial)

/-- Registration creates a retired ref only when it records that ref as cancelled.
Witness: the refused-child branch records its ref; ordinary registration installs a live
shell. Earlier retirements persist in either branch. -/
theorem State.addGroup_retired_or_cancelled (queue : State) (group : Group)
    (ref : NodeRef) (retired : (queue.addGroup group).RetiredGroup ref)
    : queue.RetiredGroup ref ∨ ref ∈ (queue.addGroup group).cancelledGroups := by
  revert retired
  unfold State.addGroup
  split
  · exact fun retired => Or.inl retired
  · dsimp only
    split
    · intro retired
      rcases List.mem_append.mp retired.1 with old | new
      · exact Or.inl ⟨old, retired.2⟩
      · exact Or.inr (List.mem_append_right _ new)
    · intro retired
      rcases List.mem_append.mp retired.1 with old | new
      · exact Or.inl ⟨old, fun live => retired.2 (by
          simpa only [List.map_append, List.map_cons, List.map_nil] using
            List.mem_append_left [group.node.ref] live)⟩
      · have same := List.mem_singleton.mp new
        exact False.elim (retired.2 (by simp [same]))

/-- Registration preserves retirement exactly for a ref not recorded as cancelled.
Witness: exclude the only new-retirement branch using its retained cancellation marker. -/
theorem State.addGroup_retired_iff (queue : State) (group : Group) (ref : NodeRef)
    (uncancelled : ref ∉ (queue.addGroup group).cancelledGroups)
    : (queue.addGroup group).RetiredGroup ref ↔ queue.RetiredGroup ref := by
  constructor
  · intro retired
    exact (queue.addGroup_retired_or_cancelled group ref retired).resolve_right uncancelled
  · exact fun retired => retired.addGroup group

/-- Batch registration reflects every retirement to the old state or cancellation list.
Witness: registration-fold induction transports earlier markers; link installation changes
neither retirement nor cancellation history, including child-first candidate order. -/
theorem State.addGroups_retired_or_cancelled (queue : State) (groups : List Group)
    (ref : NodeRef) (retired : (queue.addGroups groups).1.RetiredGroup ref)
    : queue.RetiredGroup ref ∨ ref ∈ (queue.addGroups groups).1.cancelledGroups := by
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
            let children := if node.childGroups.contains group.node.ref then node.childGroups
              else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  let property (current : State) := current.RetiredGroup ref →
    queue.RetiredGroup ref ∨ ref ∈ current.cancelledGroups
  have registered (current : State) (group : Group) (prior : property current)
      : property (current.addGroup group) := by
    intro retired
    rcases current.addGroup_retired_or_cancelled group ref retired with old | cancelled
    · exact (prior old).imp_right
        (fun member => current.addGroup_cancelledGroups_subset group member)
    · exact Or.inr cancelled
  have linked (current : State) (group : Group) (prior : property current)
      : property (link current group) := by
    unfold link
    split
    · exact prior
    · split
      · exact prior
      · intro retired
        apply prior
        exact ⟨retired.1, by simpa only [State.putGroupNode_refs] using retired.2⟩
  exact fold_preserves link property linked fresh _
    (fold_preserves State.addGroup property registered fresh queue Or.inl) retired

/-- Candidate registration preserves ancestor closure for healthy retired groups.
Witness: supported cancellation excludes new retirement of a healthy ref; old ancestor
retirements remain permanent. Support belongs to the resulting registration state. -/
theorem State.HealthyRetiredAncestors.addGroups {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (groups : List Group)
    (supported : (queue.addGroups groups).1.CancelledRecordsSupported work failed)
    : (queue.addGroups groups).1.HealthyRetiredAncestors work failed := by
  intro ref retired healthy
  have old := (queue.addGroups_retired_or_cancelled groups ref retired).resolve_right
    (supported.healthy_not_mem healthy)
  exact (prior ref old healthy).mono (fun _ retired => retired.addGroups groups)

/-- Registering task memberships preserves healthy-retirement closure.
Witness: the registry is unchanged and existing live refs are retained; old retirement
also persists, giving the exact reflection needed by the generic transport lemma. -/
theorem State.HealthyRetiredAncestors.addTask {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (task : Task)
    : (queue.addTask task).HealthyRetiredAncestors work failed := by
  apply prior.of_sameRetirements
  intro ref
  constructor
  · intro retired
    refine ⟨?_, fun live => retired.2 (queue.addTask_includesRefs task ref live)⟩
    have registered := retired.1
    rw [queue.addTask_registeredGroups task] at registered
    exact registered
  · exact fun retired => retired.addTask task

/-- Stream registration changes no group-retirement data.
Witness: inspect the empty, root, and task-linked stream branches. -/
theorem State.HealthyRetiredAncestors.addStreams {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.HealthyRetiredAncestors work failed := by
  unfold State.addStreams
  split
  · exact prior
  · dsimp
    split <;> exact prior

/-- Integration preserves healthy retirement when its cancellation history is supported.
Witness: the group stage adds no healthy retirement; tasks and streams preserve existing
retirement exactly. No contributor-availability premise is needed. -/
theorem State.HealthyRetiredAncestors.maybeIntegrateWork {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (newWork : Work)
    (parentTask : Option Occurrence := none)
    (supported
      : (queue.maybeIntegrateWork newWork parentTask).1.CancelledRecordsSupported work
          failed)
    : (queue.maybeIntegrateWork newWork parentTask).1.HealthyRetiredAncestors work
        failed := by
  exact (fold_preserves State.addTask
          (fun state => state.HealthyRetiredAncestors work failed)
          (fun _ task closure => closure.addTask task) newWork.tasks _
          (prior.addGroups newWork.groups
            (by
              simpa only [State.CancelledRecordsSupported,
                State.maybeIntegrateWork_cancelledGroups]
                using supported))).addStreams
    newWork.streams parentTask

-----------------------------------------------------------------------------------------
-- Fresh parentless records can be pruned; their descendants inherit retirement
-----------------------------------------------------------------------------------------

/-- Integration and actual pruning protect released groups, including descendants of
taskless candidates. Witness: canonical fresh roots have empty ancestry; the record-aware
pruning theorem propagates their certificates and preserves healthy retirement.
-/
theorem State.maybeIntegrateWork_prune_retirement {queue : State} {work parents failed}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (parentLinks
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (covered
      : ∀ task ∈ newWork.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ newWork.groups, group.node.ref = ref)
    (supported
      : (queue.maybeIntegrateWork newWork).1.CancelledRecordsSupported work failed)
    : let integrated := queue.maybeIntegrateWork newWork
      let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
      (∀ node ∈ pruned.2, pruned.1.AncestorsRetired work node.ref)
      ∧ (queue.HealthyRetiredAncestors work failed
          → pruned.1.HealthyRetiredAncestors work failed) := by
  have matched := matching.maybeIntegrateWork newWork known
  have linked := links.maybeIntegrateWork newWork parentLinks
  have registered := (queue.maybeIntegrateWork_registration live tasks newWork covered).1
  have protectedRoots : ∀ node ∈ (queue.maybeIntegrateWork newWork).2.newGroups,
      (queue.maybeIntegrateWork newWork).1.AncestorsRetired work node.ref := by
    intro node member
    rw [State.maybeIntegrateWork_newGroups] at member
    obtain ⟨group, candidate, same, parentless, _⟩ :=
      queue.addGroups_newGroup_candidate newWork.groups member
    obtain ⟨dependencies, record⟩ := known group candidate
    have head := parentLinks group candidate
    rw [parentless, ← canonical _ _ record] at head
    have empty : dependencies = [] := List.head?_eq_none_iff.mp head.symm
    rw [← same]
    exact .of_record generated record (by simp [empty])
  have pruned := State.pruneEmptyGroups_retirement (failed := failed)
    generated matched linked canonical
    registered _ protectedRoots
  exact ⟨
    pruned.1,
    fun prior => pruned.2 (prior.maybeIntegrateWork newWork none supported)
  ⟩

/-- Generated initialization preserves both root certificates and healthy retirement.
Witness: the empty state has no retirement; lowering gives canonical records and covered
tasks. Actual pruning may remove taskless ancestors before activating their descendants.
-/
theorem ExecutedWork.initialRetirement {work : Execution.Work}
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).RootAncestorsRetired work
      ∧ (State.initialize (Work.fromExecution work)).HealthyRetiredAncestors work [] := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have pruned := State.maybeIntegrateWork_prune_retirement (queue := {}) (failed := [])
    generated (by intro node member; cases member) (by intro node member; cases member)
    canonical (by intro node member; cases member) (by intro task member; cases member)
    (Work.fromExecution work)
    (fun group member =>
      let ⟨dependencies, record, _⟩ := workFromSpec_groups_recordAt Located.root member
      ⟨dependencies, record⟩)
    (fun group member => workFromSpec_groups_parentCanonical Located.root canonical member)
    (workFromSpec_immediateGroupsCoverTasks work [])
    (by intro ref member
        rw [State.maybeIntegrateWork_cancelledGroups,
          State.addGroups_cancelledGroups_empty rfl] at member
        exact False.elim (List.not_mem_nil member))
  let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let result := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := result.2 }
  refine ⟨?_, (pruned.2 ?_).startNewWork released⟩
  · intro ref active
    rw [createWorkQueue_rootGroups] at active
    obtain ⟨node, member, same⟩ := List.mem_map.mp active
    exact same ▸ (pruned.1 node member).mono
      (fun _ retired => retired.startNewWork released)
  · intro ref retired
    exact False.elim (List.not_mem_nil retired.1)

/-- Generated initialization has ancestor-closed healthy retirement, without assuming
an initialization-notice law. Witness: the joint initialization certificate.
-/
theorem createWorkQueue_healthyRetiredAncestors {work : Execution.Work}
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).HealthyRetiredAncestors work [] :=
  generated.initialRetirement.2

/-- Generated initial roots retain every task-bearing ancestor's retirement certificate.
Witness: the joint initialization theorem accounts for taskless-root pruning.
-/
theorem ExecutedWork.initialRootAncestorsRetired {work : Execution.Work}
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).RootAncestorsRetired work :=
  generated.initialRetirement.1

/-- A matching stream item preserves root and healthy-retirement certificates.
Witness: old roots survive; fresh parentless candidates pass through actual pruning,
which may promote descendants with nonempty but already-retired ancestry.
-/
theorem State.integrateStreamItem_retirement {queue : State} {work parents failed}
    (generated : ExecutedWork work) (groups : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (protectedRoots : queue.RootAncestorsRetired work)
    (retirement : queue.HealthyRetiredAncestors work failed)
    {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (supported
      : (queue.maybeIntegrateWork item.work).1.CancelledRecordsSupported work failed)
    : (queue.integrateStreamItem item).RootAncestorsRetired work
      ∧ (queue.integrateStreamItem item).HealthyRetiredAncestors work failed := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  have certificates := queue.maybeIntegrateWork_prune_retirement generated groups links
    canonical live tasks item.work
    (fun _ candidate => matching.streamItem_childGroups_recordAt member candidate)
    (fun _ candidate => matching.streamItem_childGroups_parentCanonical canonical member candidate)
    (matching.streamItem_childTasksCovered member) supported
  refine ⟨?_, (certificates.2 retirement).startNewWork released⟩
  intro ref active
  change ref ∈ (pruned.1.startNewWork released).rootGroups at active
  rw [(pruned.1.startNewWork_groupCore released).2.2] at active
  rcases List.mem_append.mp active with old | added
  · change ref ∈ (integrated.1.pruneEmptyGroups integrated.2.newGroups).1.rootGroups at old
    rw [State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups] at old
    exact (protectedRoots ref old).mono (fun _ retired =>
      ((retired.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups).startNewWork
        released)
  · obtain ⟨node, announced, same⟩ := List.mem_map.mp added
    exact same ▸ (certificates.1 node announced).mono
      (fun _ retired => retired.startNewWork released)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
