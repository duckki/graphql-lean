import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitializationSpecialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationCandidates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation

/-! Integration and initialization preserve healthy retired-ancestor certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Refused registration inherits retirement from its absent registered parent
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

/-- A newly retired registration was refused because its immediate parent was absent.
Witness: every successful installation retains old live refs and installs its own shell;
only the absent-parent branch can register a new ref without a live record.
-/
theorem State.addGroup_retired_origin (queue : State) (group : Group)
    (ref : NodeRef) (retired : (queue.addGroup group).RetiredGroup ref)
    : queue.RetiredGroup ref
      ∨ ref = group.node.ref
        ∧ ref ∉ queue.registeredGroups
        ∧ ∃ parent, group.parent = some parent ∧ queue.groupNode? parent = none := by
  by_cases old : ref ∈ queue.registeredGroups
  · exact .inl ⟨old, fun live => retired.2 (queue.addGroup_refs_subset group live)⟩
  have same : ref = group.node.ref := by
    rcases List.mem_append.mp (queue.addGroup_registeredGroups_subset group retired.1) with
      prior | fresh
    · exact False.elim (old prior)
    · exact List.mem_singleton.mp fresh
  refine .inr ⟨same, old, ?_⟩
  subst ref
  unfold State.addGroup at retired
  split at retired
  · exact False.elim (old retired.1)
  · split at retired
    · exact False.elim (retired.2 (by simp))
    · rename_i parent parentEq
      split at retired
      · exact ⟨parent, parentEq, ‹queue.groupNode? parent = none›⟩
      · exact False.elim (retired.2 (by rw [State.putGroupNode_refs]; simp))

/-- Refusal below a registered parent inherits that parent's retirement certificate.
Witness: successful parent completion and failure removal both leave permanent retirement;
a healthy child's ancestry is healthy, so the parent's certificate extends to the child.
-/
theorem State.HealthyRetiredAncestors.addGroup {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (generated : ExecutedWork work)
    (group : Group)
    (matching
      : ∃ dependencies,
          GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head?)
    (parentRegistered
      : ∀ parent, group.parent = some parent → parent ∈ queue.registeredGroups)
    : (queue.addGroup group).HealthyRetiredAncestors work failed := by
  intro ref retired healthy
  rcases queue.addGroup_retired_origin group ref retired with old | ⟨same, _, parent, head, absent⟩
  · exact (prior ref old healthy).mono (fun _ retired => retired.addGroup group)
  subst ref
  obtain ⟨dependencies, known, canonical⟩ := matching
  have parentHead : dependencies.head? = some parent := canonical.symm.trans head
  cases dependencies with
  | nil => cases parentHead
  | cons first rest =>
      have equal : first = parent := Option.some.inj parentHead
      subst first
      obtain ⟨parentNode, parentRef, parentKnown⟩ := known.parent
      have parentRetired : queue.RetiredGroup parent :=
        .of_lookup_none (parentRegistered parent head) absent
      have parentHealthy : ¬GroupRecordInvalidated work failed parent :=
        fun invalid => healthy (.ancestor known List.mem_cons_self invalid)
      have ancestors := State.AncestorsRetired.child generated known parentKnown
        (by simp [parentRef])
        (prior parentNode.ref (parentRef.symm ▸ parentRetired)
          (parentRef.symm ▸ parentHealthy))
        (parentRef.symm ▸ parentRetired)
      exact ancestors.mono (fun _ retired => retired.addGroup group)

/-- Parent-first registration preserves healthy retired ancestry, including refused children.
Witness: execution-derived parent closure ensures the missing parent is already registered
at each installation. Its permanent retirement supplies the child's ancestor certificate.
-/
theorem State.HealthyRetiredAncestors.addGroups {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (groups : List Group)
    (generated : ExecutedWork work) (coverage : queue.LiveGroupsRegistered)
    (matching
      : ∀ group ∈ groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ groups,
          ∀ parent,
            group.parent = some parent
            → parent ∈ queue.registeredGroups ++ groups.map (fun group => group.node.ref))
    : (queue.addGroups groups).1.HealthyRetiredAncestors work failed := by
  let property (current : State) := current.HealthyRetiredAncestors work failed
    ∧ queue.registeredGroups ⊆ current.registeredGroups
  have ordered : ∀ group ∈ groups, ∀ parent, group.parent = some parent → parent < group.node.ref := by
    intro group member parent parentEq
    obtain ⟨dependencies, known, canonical⟩ := matching group member
    exact generated.groupRecordAncestorSmaller known
      (List.mem_of_head? (canonical.symm.trans parentEq))
  exact (State.addGroups_preserves_parentRegistered property groups ordered
          (fun current group member _ parents valid =>
            ⟨
              valid.1.addGroup generated group (matching group member)
                (fun parent parentEq =>
                  (List.mem_append.mp (closed group member parent parentEq)).elim
                    (fun known => valid.2 known) (parents parent parentEq)),
              valid.2.trans (current.addGroup_registeredGroups_subset_old group)
            ⟩)
          queue coverage ⟨prior, List.Subset.refl _⟩).1

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

/-- Integration retains healthy retired ancestry through parent-first registration.
Witness: source declarations close the candidate parents; tasks and streams retain
permanent retirement after the group stage.
-/
theorem State.HealthyRetiredAncestors.maybeIntegrateWork {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (newWork : Work)
    (parentTask : Option Occurrence := none)
    (generated : ExecutedWork work) (coverage : queue.LiveGroupsRegistered)
    (matching
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ newWork.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ newWork.groups.map (fun group => group.node.ref))
    : (queue.maybeIntegrateWork newWork parentTask).1.HealthyRetiredAncestors work
        failed := by
  exact (fold_preserves State.addTask
    (fun state => state.HealthyRetiredAncestors work failed)
    (fun _ task closure => closure.addTask task) newWork.tasks _
    (prior.addGroups newWork.groups generated coverage matching closed)).addStreams
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
    (closed
      : ∀ group ∈ newWork.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ newWork.groups.map (fun group => group.node.ref))
    : let integrated := queue.maybeIntegrateWork newWork
      let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
      (∀ node ∈ pruned.2, pruned.1.AncestorsRetired work node.ref)
      ∧ (queue.HealthyRetiredAncestors work failed
          → pruned.1.HealthyRetiredAncestors work failed) := by
  have matched := matching.maybeIntegrateWork newWork known
  have linked := links.maybeIntegrateWork newWork parentLinks
  have registered := (queue.maybeIntegrateWork_registration live tasks newWork
    (by intro task member ref contributor; exact Or.inr (covered task member ref contributor))).1
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
    fun prior =>
      pruned.2
        (prior.maybeIntegrateWork newWork none generated live
          (by
            intro group member
            obtain ⟨dependencies, record⟩ := known group member
            exact ⟨
              dependencies,
              record,
              by rw [canonical _ _ record]; exact parentLinks group member
            ⟩)
          closed)
  ⟩

/-- Generated initialization preserves both root certificates and healthy retirement.
Witness: the empty state has no retirement; lowering gives canonical records and covered
tasks. Actual pruning may remove taskless ancestors before activating their descendants.
-/
theorem ExecutedWork.initialRetirement {work : Execution.Work}
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).RootAncestorsRetired work
      ∧ (State.initialize (Work.fromExecution work)).HealthyRetiredAncestors work [] := by
  rw [State.initialize_empty_eq_activation]
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have pruned := State.maybeIntegrateWork_prune_retirement (queue := {}) (failed := [])
    generated (by intro node member; cases member) (by intro node member; cases member)
    canonical (by intro node member; cases member) (by intro task member; cases member)
    (Work.fromExecution work)
    (fun group member =>
      let ⟨dependencies, record, _⟩ := workFromSpec_groups_recordAt_root member
      ⟨dependencies, record⟩)
    (fun group member => workFromSpec_groups_parentCanonical_root canonical member)
    (workFromSpec_immediateGroupsCoverTasks work [] generated.declarations)
    (by
      intro group member parent parentEq
      have certificate := generated.declarations.lower (Located.root (root := work))
      rcases certificate.parents group member parent parentEq with old | candidate
      · cases old
      · obtain ⟨candidate, included, same⟩ := candidate
        exact List.mem_append_right _ (List.mem_map.mpr ⟨candidate, included, same⟩))
  let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let result := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := result.2 }
  have emptyReject : ({} : State).TaskRejectionsSatisfy (fun _ _ => False) := by
    intro node member; cases member
  have prunedReject := (emptyReject.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups
    integrated.2.newGroups
  have clean : ∀ node ∈ result.1.taskNodes, node.rejection = none := by
    intro node member
    cases rejected : node.rejection with
    | none => rfl
    | some errors => exact (prunedReject node member errors rejected).elim
  refine ⟨?_, (pruned.2 ?_).startNewWork_of_no_cached_failures released clean⟩
  · intro ref active
    change ref ∈ (State.initialize (Work.fromExecution work)).rootGroups at active
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
    (_supported
      : (queue.maybeIntegrateWork item.work).1.CancelledRecordsSupported work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (available : List (Occurrence × Nat) := [])
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.integrateStreamItem item available).RootAncestorsRetired work
      ∧ (queue.integrateStreamItem item available).HealthyRetiredAncestors work
          failed := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  have certificates := queue.maybeIntegrateWork_prune_retirement (failed := failed) generated groups links
    canonical live tasks item.work
    (fun _ candidate => matching.streamItem_childGroups_recordAt member candidate)
    (fun _ candidate => matching.streamItem_childGroups_parentCanonical canonical member candidate)
    (matching.streamItem_childTasksCovered generated.declarations member)
    (by
      intro group candidate parent parentEq
      have certificate := generated.declarations.sourceStreamItem matching member queue.registeredGroups
      rcases certificate.parents group candidate parent parentEq with old | fresh
      · exact List.mem_append_left _ old
      · obtain ⟨candidate, included, same⟩ := fresh
        exact List.mem_append_right _ (List.mem_map.mpr ⟨candidate, included, same⟩))
  have childTasks : ∀ task ∈ item.work.tasks, TaskMatches work task := by
    intro task taskMember
    obtain ⟨address, payload, same, known⟩ :=
      matching.streamItem_childTask_producer member taskMember
    exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
      matching.streamItem_childTask_groupsExact member taskMember⟩
  refine ⟨
    ?_,
    (certificates.2 retirement).startNewWork
      ((cached.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups)
      ((registered.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups)
      ((tasksMatch.maybeIntegrateWork item.work childTasks).pruneEmptyGroups
        integrated.2.newGroups)
      ((sound.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups)
      ((links.maybeIntegrateWork item.work
          (fun _ candidate =>
            matching.streamItem_childGroups_parentCanonical canonical member
              candidate)).pruneEmptyGroups
        integrated.2.newGroups)
      ((groups.maybeIntegrateWork item.work
          (fun _ candidate =>
            matching.streamItem_childGroups_recordAt member candidate)).pruneEmptyGroups
        integrated.2.newGroups)
      canonical released available recorded
  ⟩
  intro ref active
  change ref ∈ (pruned.1.startNewWork released available).1.rootGroups at active
  have active := (pruned.1.startNewWork_rootGroups_sublist released available).subset active
  rcases List.mem_append.mp active with old | added
  · change ref ∈ (integrated.1.pruneEmptyGroups integrated.2.newGroups).1.rootGroups at old
    rw [State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups] at old
    exact (protectedRoots ref old).mono (fun _ retired =>
      ((retired.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups).startNewWork
        released available)
  · obtain ⟨node, announced, same⟩ := List.mem_map.mp added
    exact same ▸ (certificates.1 node announced).mono
      (fun _ retired => retired.startNewWork released available)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
