import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledOwners
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentCutsHandlers

/-! Cancellation-marker closure for task-bearing ancestors of uncancelled retirements.
The evidence describes existing registration and cancellation fields, without a runtime cache.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Each task-bearing defer ancestor of this ref has no actual cancellation marker. -/
def State.AncestorsUncancelled (queue : State) (work : Execution.Work) (ref : NodeRef)
    : Prop :=
  ∀ node dependencies,
    GroupRecordAt work node dependencies
    → node.ref = ref
    → ∀ ancestor ∈ dependencies,
        ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → ancestor ∈ owners
          → ancestor ∉ queue.cancelledGroups

/-- Uncancelled retired records retain uncancelled task-bearing ancestors.
This is proof evidence over permanent markers, separately from any source-failure inventory.
-/
def State.UncancelledRetiredMarkers (queue : State) (work : Execution.Work) : Prop :=
  ∀ ref,
    queue.RetiredGroup ref
    → ref ∉ queue.cancelledGroups
    → queue.AncestorsUncancelled work ref

/-- Empty cancellation history establishes ancestor-marker closure for any retirement set. -/
theorem State.UncancelledRetiredMarkers.of_empty {queue : State} (work : Execution.Work)
    (empty : queue.cancelledGroups = [])
    : queue.UncancelledRetiredMarkers work := by
  intro ref _ _ node dependencies known same ancestor member occurrence owners task contributes
  rw [empty]
  exact List.not_mem_nil

/-- Unchanged retirement and cancellation sets transport the marker certificate. -/
theorem State.UncancelledRetiredMarkers.of_sameRetirements {before after : State} {work}
    (prior : before.UncancelledRetiredMarkers work)
    (same : ∀ ref, after.RetiredGroup ref ↔ before.RetiredGroup ref)
    (cancelled : after.cancelledGroups = before.cancelledGroups)
    : after.UncancelledRetiredMarkers work := by
  intro ref retired uncancelled node dependencies known identity ancestor member occurrence owners
    task contributes
  rw [cancelled] at uncancelled ⊢
  exact prior ref ((same ref).mp retired) uncancelled node dependencies known identity ancestor
    member occurrence owners task contributes

/-- Cache exposure preserves exact ancestor markers and retirement sets. -/
theorem State.UncancelledRetiredMarkers.cacheTaskFailures {queue : State} {work}
    (prior : queue.UncancelledRetiredMarkers work) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).UncancelledRetiredMarkers work := by
  apply prior.of_sameRetirements
  · intro ref
    simp only [State.RetiredGroup, State.cacheTaskFailures_registeredGroups,
      State.cacheTaskFailures_groupNodes]
  · exact queue.cacheTaskFailures_cancelledGroups available

/-- Task metadata replacement changes neither ancestor markers nor retirements. -/
theorem State.UncancelledRetiredMarkers.putTaskNode {queue : State} {work}
    (prior : queue.UncancelledRetiredMarkers work) (updated : TaskNode)
    : (queue.putTaskNode updated).UncancelledRetiredMarkers work :=
  prior

/-- Membership cleanup preserves the same registered, live and cancelled refs. -/
theorem State.UncancelledRetiredMarkers.removeTask {queue : State} {work}
    (prior : queue.UncancelledRetiredMarkers work) (occurrence : Occurrence)
    : (queue.removeTask occurrence).UncancelledRetiredMarkers work := by
  apply prior.of_sameRetirements
  · intro ref
    simp only [State.RetiredGroup, State.removeTask, List.map_map, Function.comp_def]
  · rfl

/-- Group metadata replacement retains exact retirement and cancellation coordinates. -/
theorem State.UncancelledRetiredMarkers.putGroupNode {queue : State} {work}
    (prior : queue.UncancelledRetiredMarkers work) (updated : GroupNode)
    : (queue.putGroupNode updated).UncancelledRetiredMarkers work := by
  apply prior.of_sameRetirements
  · intro ref
    simp only [State.RetiredGroup, State.putGroupNode_refs]
    rfl
  · rfl

/-- A live record's ancestors are uncancelled when missing parents have retired certificates.
Witness: follow the exact parent chain; a live parent recurses to a shorter chain, while
an absent registered parent uses its uncancelled-retirement marker certificate.
-/
theorem State.UncancelledRetiredMarkers.live_record_ancestors {queue : State}
    {work parents} (prior : queue.UncancelledRetiredMarkers work)
    (safe : queue.LiveParentsUncancelled) (fields : queue.GroupParentsCanonical parents)
    (registry : queue.ParentRegistryClosed parents)
    (registered : queue.LiveGroupsRegistered)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {record dependencies} (known : GroupRecordAt work record dependencies)
    (live : ∃ node ∈ queue.groupNodes, node.group.node.ref = record.ref)
    : ∀ ancestor ∈ dependencies,
        ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → ancestor ∈ owners
          → ancestor ∉ queue.cancelledGroups := by
  induction dependencies generalizing record with
  | nil => intro ancestor impossible; cases impossible
  | cons parent rest ih =>
      obtain ⟨node, member, same⟩ := live
      have parentEq : node.group.parent = some parent := by
        rw [fields node member, same, ← canonical record (parent :: rest) known]
        rfl
      have parentSafe := safe node member parent parentEq
      have parentRegistered := registry.parent_registered registered fields member parentEq
      obtain ⟨parentRecord, parentRef, parentKnown⟩ := known.parent
      have tailSafe : ∀ ancestor ∈ rest, ∀ occurrence owners,
          TaskHasOwners work occurrence owners
            → ancestor ∈ owners → ancestor ∉ queue.cancelledGroups := by
        cases found : queue.groupNode? parent with
        | none =>
            exact prior parentRecord.ref
              (.of_lookup_none (parentRef.symm ▸ parentRegistered) (parentRef.symm ▸ found))
              (parentRef.symm ▸ parentSafe) parentRecord rest parentKnown rfl
        | some parentNode =>
            exact ih parentKnown ⟨parentNode, List.mem_of_find?_eq_some found,
              (State.groupNode?_ref found).trans parentRef.symm⟩
      intro ancestor included occurrence owners task contributes
      rcases List.mem_cons.mp included with same | later
      · exact same ▸ parentSafe
      · exact tailSafe ancestor later occurrence owners task contributes

/-- A closed permanent registry contains every ancestor in a known record's exact chain. -/
theorem State.ParentRegistryClosed.ancestorsRegistered {queue : State} {work parents}
    (registry : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {record dependencies} (known : GroupRecordAt work record dependencies)
    (registered : record.ref ∈ queue.registeredGroups)
    : dependencies.Subset queue.registeredGroups := by
  induction dependencies generalizing record with
  | nil => exact List.nil_subset _
  | cons parent rest ih =>
      have parentRegistered := registry record.ref registered parent (by
        rw [← canonical record (parent :: rest) known]
        rfl)
      obtain ⟨parentRecord, same, parentKnown⟩ := known.parent
      have tail := ih parentKnown (same.symm ▸ parentRegistered)
      intro ancestor member
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ parentRegistered
      · exact tail later

private theorem addGroup_registered_cancellation {queue : State} {ref : NodeRef}
    (registered : ref ∈ queue.registeredGroups) (group : Group)
    (recorded : ref ∈ (queue.addGroup group).cancelledGroups)
    : ref ∈ queue.cancelledGroups := by
  by_cases marked : ref ∈ queue.cancelledGroups
  · exact marked
  unfold State.addGroup at recorded
  split at recorded
  · exact recorded
  · rename_i guard
    have fresh : group.node.ref ∉ queue.registeredGroups
        ∧ queue.groupNode? group.node.ref = none := by simpa using guard
    split at recorded
    · exact recorded
    · split at recorded
      · split at recorded
        · rcases List.mem_append.mp recorded with old | new
          · exact old
          · exact False.elim (fresh.1 (List.mem_singleton.mp new ▸ registered))
        · exact recorded
      · exact recorded

/-- Group registration cannot add a cancellation marker to an already registered ref. -/
theorem State.addGroups_registered_cancellation (queue : State) (groups : List Group)
    {ref : NodeRef} (registered : ref ∈ queue.registeredGroups)
    (recorded : ref ∈ (queue.addGroups groups).1.cancelledGroups)
    : ref ∈ queue.cancelledGroups := by
  let property (current : State) := ref ∈ current.registeredGroups
    ∧ (ref ∈ current.cancelledGroups → ref ∈ queue.cancelledGroups)
  have final := State.addGroups_preserves property groups (fun current group _ prior =>
    ⟨current.addGroup_registeredGroups_subset_old group prior.1,
      fun marked => prior.2 (addGroup_registered_cancellation prior.1 group marked)⟩)
    queue ⟨registered, fun member => member⟩
  exact final.2 recorded

/-- A refused uncancelled child inherits its absent parent's cancellation exclusion.
Old ancestors were registered before installation, so a fresh marker cannot be added to them.
-/
theorem State.UncancelledRetiredMarkers.addGroup {queue : State} {work parents}
    (prior : queue.UncancelledRetiredMarkers work)
    (registry : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (group : Group) (parentField : group.parent = (parents group.node.ref).head?)
    (parentRegistered
      : ∀ parent, group.parent = some parent → parent ∈ queue.registeredGroups)
    : (queue.addGroup group).UncancelledRetiredMarkers work := by
  intro ref retired uncancelled node dependencies known identity ancestor member occurrence owners
    task contributes recorded
  rcases queue.addGroup_retired_origin group ref retired with old |
    ⟨same, fresh, parent, head, absent⟩
  · have oldUncancelled : ref ∉ queue.cancelledGroups := fun member =>
      uncancelled (queue.addGroup_cancelledGroups_subset group member)
    have ancestorRegistered := registry.ancestorsRegistered canonical known
      (identity.symm ▸ old.1)
    exact prior ref old oldUncancelled node dependencies known identity ancestor member
      occurrence owners task contributes
      (addGroup_registered_cancellation (ancestorRegistered member) group recorded)
  subst ref
  have missing : queue.groupNode? group.node.ref = none := by
    apply (queue.groupNode?_eq_none_iff _).mpr
    intro live
    exact retired.2 (same.symm ▸ queue.addGroup_refs_subset group live)
  have parentUncancelled : parent ∉ queue.cancelledGroups := by
    intro marked
    apply uncancelled
    rw [same]
    simp [State.addGroup, same ▸ fresh, missing, head, absent, marked]
  have parentRetired : queue.RetiredGroup parent :=
    .of_lookup_none (parentRegistered parent head) absent
  have parentHead : dependencies.head? = some parent := by
    rw [canonical _ _ known, same, ← parentField, head]
  cases dependencies with
  | nil => cases parentHead
  | cons first rest =>
      have equal : first = parent := Option.some.inj parentHead
      subst first
      rcases List.mem_cons.mp member with same | above
      · subst ancestor
        exact parentUncancelled (addGroup_registered_cancellation parentRetired.1 group recorded)
      · obtain ⟨parentNode, parentRef, parentKnown⟩ := known.parent
        have registered := registry.ancestorsRegistered canonical parentKnown
          (parentRef.symm ▸ parentRetired.1)
        exact prior parent parentRetired parentUncancelled parentNode rest parentKnown parentRef
          ancestor above occurrence owners task contributes
          (addGroup_registered_cancellation (registered above) group recorded)

/-- Recursive installation retains uncancelled ancestor markers without assuming list order.
Witness: candidate parents are registered first; a refused child's uncancelled parent and
its earlier ancestors supply the exclusion certificate at that actual boundary.
-/
theorem State.UncancelledRetiredMarkers.addGroups {queue : State} {work parents}
    (prior : queue.UncancelledRetiredMarkers work)
    (registry : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (groups : List Group) (generated : ExecutedWork work)
    (live : queue.LiveGroupsRegistered)
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
    : (queue.addGroups groups).1.UncancelledRetiredMarkers work := by
  let property (current : State) := current.UncancelledRetiredMarkers work
    ∧ current.ParentRegistryClosed parents ∧ queue.registeredGroups ⊆ current.registeredGroups
  have ordered : ∀ group ∈ groups, ∀ parent, group.parent = some parent → parent < group.node.ref := by
    intro group member parent parentEq
    obtain ⟨dependencies, known, field⟩ := matching group member
    exact generated.groupRecordAncestorSmaller known
      (List.mem_of_head? (field.symm.trans parentEq))
  exact (State.addGroups_preserves_parentRegistered property groups ordered
          (fun current group member _ visited valid => by
            obtain ⟨dependencies, known, field⟩ := matching group member
            have parentField : group.parent = (parents group.node.ref).head? := by
              rwa [canonical _ _ known] at field
            have parentKnown
                : ∀ parent,
                    group.parent = some parent → parent ∈ current.registeredGroups := by
              intro parent parentEq
              exact (List.mem_append.mp (closed group member parent parentEq)).elim
                (fun known => valid.2.2 known) (visited parent parentEq)
            refine ⟨
              valid.1.addGroup valid.2.1 canonical group parentField parentKnown,
              ?_,
              valid.2.2.trans (current.addGroup_registeredGroups_subset_old group)
            ⟩
            intro ref registered parent head
            have retained := current.addGroup_registeredGroups_subset_old group
            rcases List.mem_append.mp (current.addGroup_registeredGroups_subset group registered) with old | fresh
            · exact retained (valid.2.1 ref old parent head)
            · obtain rfl := List.mem_singleton.mp fresh
              exact retained (parentKnown parent (parentField.trans head)))
          queue live ⟨prior, registry, List.Subset.refl _⟩).1

/-- Task installation preserves the same retired refs and cancellation history. -/
theorem State.UncancelledRetiredMarkers.addTask {queue : State} {work}
    (prior : queue.UncancelledRetiredMarkers work) (task : Task)
    : (queue.addTask task).UncancelledRetiredMarkers work := by
  apply prior.of_sameRetirements
  · intro ref
    constructor
    · intro retired
      refine ⟨?_, fun live => retired.2 (queue.addTask_includesRefs task ref live)⟩
      have registered := retired.1
      rwa [State.addTask_registeredGroups] at registered
    · exact fun retired => retired.addTask task
  · exact queue.addTask_cancelledGroups task

/-- Source attachment leaves ancestor markers and group retirement data unchanged. -/
theorem State.UncancelledRetiredMarkers.addStreams {queue : State} {work}
    (prior : queue.UncancelledRetiredMarkers work) (streams : List Stream)
    (producer : Option Occurrence := none)
    : (queue.addStreams streams producer).1.UncancelledRetiredMarkers work := by
  unfold State.addStreams
  split
  · exact prior
  · dsimp only
    split <;> exact prior

/-- Complete scope registration preserves uncancelled retired ancestor markers. -/
theorem State.UncancelledRetiredMarkers.maybeIntegrateWork {queue : State} {work parents}
    (prior : queue.UncancelledRetiredMarkers work)
    (registry : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (incoming : Work) (producer : Option Occurrence := none)
    (generated : ExecutedWork work) (live : queue.LiveGroupsRegistered)
    (matching
      : ∀ group ∈ incoming.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ incoming.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ incoming.groups.map (fun group => group.node.ref))
    : (queue.maybeIntegrateWork incoming producer).1.UncancelledRetiredMarkers work := by
  have fold (tasks : List Task) (current : State)
      (markers : current.UncancelledRetiredMarkers work)
      : (tasks.foldl State.addTask current).UncancelledRetiredMarkers work := by
    induction tasks generalizing current with
    | nil => exact markers
    | cons task rest ih => exact ih _ (markers.addTask task)
  exact (fold incoming.tasks _
          (prior.addGroups registry canonical incoming.groups generated live matching
            closed)).addStreams
    incoming.streams producer

/-- Successful ref filtering installs its ancestor-marker certificate as a retirement. -/
theorem State.UncancelledRetiredMarkers.filter_parent {queue : State} {work}
    (prior : queue.UncancelledRetiredMarkers work) (closedRef : NodeRef)
    (ancestors : queue.AncestorsUncancelled work closedRef)
    : ({
            queue with
              groupNodes :=
                queue.groupNodes.filter (fun node => node.group.node.ref != closedRef)
              rootGroups := queue.rootGroups.filter (· != closedRef)
          }
        : State).UncancelledRetiredMarkers
        work := by
  intro ref retired uncancelled
  by_cases same : ref = closedRef
  · exact same.symm ▸ ancestors
  · have oldRetired : queue.RetiredGroup ref := by
      refine ⟨retired.1, ?_⟩
      intro present
      obtain ⟨node, member, identity⟩ := List.mem_map.mp present
      have different : node.group.node.ref ≠ closedRef := by rwa [identity]
      exact retired.2 (List.mem_map.mpr ⟨node,
        List.mem_filter.mpr ⟨member, by simpa only [bne_iff_ne] using different⟩, identity⟩)
    exact prior ref oldRetired uncancelled

private structure MarkerFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs)
    : Prop where
  markers : queue.UncancelledRetiredMarkers work
  safe : queue.LiveParentsUncancelled
  fields : queue.GroupParentsCanonical parents
  registry : queue.ParentRegistryClosed parents
  live : queue.LiveGroupsRegistered

private theorem MarkerFrame.removeTask {queue work parents}
    (frame : MarkerFrame queue work parents) (occurrence : Occurrence)
    : MarkerFrame (queue.removeTask occurrence) work parents := by
  refine ⟨frame.markers.removeTask _, frame.safe.removeTask _, frame.fields.removeTask _,
    frame.registry, ?_⟩
  intro node member
  change node ∈ queue.groupNodes.map _ at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  rw [← same]
  exact frame.live old oldMember

private theorem MarkerFrame.filter_parent {queue work parents}
    (frame : MarkerFrame queue work parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (node : GroupNode) (member : node ∈ queue.groupNodes)
    : MarkerFrame
        ({
              queue with
                groupNodes :=
                  queue.groupNodes.filter
                    (fun entry => entry.group.node.ref != node.group.node.ref)
            }
          : State)
        work parents := by
  have ancestors : queue.AncestorsUncancelled work node.group.node.ref := by
    intro record dependencies known identity
    exact frame.markers.live_record_ancestors frame.safe frame.fields frame.registry frame.live
      canonical known ⟨node, member, identity.symm⟩
  have removed := frame.markers.filter_parent node.group.node.ref ancestors
  exact ⟨removed, frame.safe.of_subset List.filter_sublist.subset rfl,
    fun entry kept => frame.fields entry (List.mem_filter.mp kept).1,
    frame.registry, fun entry kept => frame.live entry (List.mem_filter.mp kept).1⟩

/-- Empty-shell pruning preserves uncancelled retired ancestor markers.
Witness: each selected live shell has uncancelled ancestors from the exact parent chain;
filtering installs its certificate before considering released descendants.
-/
theorem State.UncancelledRetiredMarkers.pruneEmptyGroups {queue : State} {work parents}
    (prior : queue.UncancelledRetiredMarkers work) (safe : queue.LiveParentsUncancelled)
    (fields : queue.GroupParentsCanonical parents)
    (registry : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.UncancelledRetiredMarkers work := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (frame : MarkerFrame current work parents)
      : MarkerFrame (State.pruneEmptyGroups.go fuel current remaining kept).1 work parents := by
    induction fuel generalizing current remaining kept with
    | zero => exact frame
    | succ fuel ih =>
        cases remaining with
        | nil => exact frame
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih current rest kept frame
            · rename_i node found
              split
              · have filtered :=
                  frame.filter_parent canonical node (List.mem_of_find?_eq_some found)
                have same := State.groupNode?_ref found
                rw [same] at filtered
                exact ih _ _ kept filtered
              · exact ih current rest (kept ++ [group]) frame
  exact (loop _ queue groups [] ⟨prior, safe, fields, registry, live⟩).markers

/-- Successful group closure installs ancestor-marker certificates before child pruning.
Witness: task flushing preserves the structural frame and the closing ref's live record;
that record's exact parent chain certifies its retirement and every subsequent prune.
-/
theorem State.UncancelledRetiredMarkers.finishGroupSuccess {queue : State} {work parents}
    (prior : queue.UncancelledRetiredMarkers work) (safe : queue.LiveParentsUncancelled)
    (fields : queue.GroupParentsCanonical parents)
    (registry : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (group : GroupNode) (member : group ∈ queue.groupNodes)
    : (queue.finishGroupSuccess group).1.UncancelledRetiredMarkers work := by
  have flush (tasks : List Occurrence)
      (acc : State × List Execution.ExecutionGroupValue × NodeRefs)
      (frame : MarkerFrame acc.1 work parents)
      (present : group.group.node.ref ∈ acc.1.groupNodes.map (fun node => node.group.node.ref))
      : MarkerFrame (tasks.foldl flushGroupTask acc).1 work parents
        ∧ group.group.node.ref ∈ (tasks.foldl flushGroupTask acc).1.groupNodes.map
          (fun node => node.group.node.ref) := by
    induction tasks generalizing acc with
    | nil => exact ⟨frame, present⟩
    | cons occurrence rest ih =>
        rw [List.foldl_cons]
        unfold flushGroupTask
        dsimp only
        split
        · exact ih _ frame present
        · apply ih _ (frame.removeTask occurrence)
          simpa only [State.removeTask, List.map_map, Function.comp_def] using present
  let flushed := group.tasks.foldl flushGroupTask (queue, [], [])
  have result := flush group.tasks (queue, [], []) ⟨prior, safe, fields, registry, live⟩
    (List.mem_map.mpr ⟨group, member, rfl⟩)
  obtain ⟨node, member, same⟩ := List.mem_map.mp result.2
  have filtered := result.1.filter_parent canonical node member
  rw [same] at filtered
  let current : State := { flushed.1 with
    groupNodes := flushed.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref) }
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  have frame : MarkerFrame current work parents :=
    ⟨filtered.markers, filtered.safe, filtered.fields, filtered.registry, filtered.live⟩
  change (current.pruneEmptyGroups children).1.UncancelledRetiredMarkers work
  exact frame.markers.pruneEmptyGroups frame.safe frame.fields frame.registry frame.live
    canonical children

/-- Failure removal cannot add an ancestor marker to an uncancelled retired record.
Witness: a new marker inherits the root's single task cause. Cancellation-aware accounting
excludes that fresh task from every uncancelled retired contributor in the target ancestry.
-/
theorem State.UncancelledRetiredMarkers.removeGroup {queue : State} {work parents settled}
    (prior : queue.UncancelledRetiredMarkers work)
    (structural : queue.UncancelledRetiredAncestors work)
    (accounted : queue.UncancelledTaskAccounting settled) (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {task : Task} (registered : task ∈ queue.tasks) (taskKnown : TaskMatches work task)
    (fresh : task.occurrence ∉ settled) (root : NodeRef)
    (invalid : GroupRecordInvalidated work [task.occurrence] root)
    : (queue.removeGroup root).UncancelledRetiredMarkers work := by
  intro ref retired uncancelled node dependencies known identity ancestor member occurrence owners
    ownerKnown contributes recorded
  have old := queue.removeGroup_missing_uncancelled root ref retired.lookup_none uncancelled
  have oldRetired : queue.RetiredGroup ref := .of_lookup_none retired.1 old.1
  have markers := prior ref oldRetired old.2
  have absent := markers node dependencies known identity ancestor member occurrence owners
    ownerKnown contributes
  have cause := queue.removeGroup_newCancelled_invalidated links matching canonical root invalid
    recorded absent
  have noFailure := (identity.symm ▸ oldRetired).healthy_cons_fresh_of_uncancelledAccounting
    (identity.symm ▸ structural ref oldRetired old.2) (identity.symm ▸ old.2)
    (fun ancestor member occurrence owners ownerKnown contributes =>
      markers node dependencies known identity ancestor member occurrence owners ownerKnown
        contributes)
    generated known (fun failure => failure.nonempty rfl) accounted registered taskKnown fresh
  exact noFailure (.ancestor known member cause)

/-- A task's uncancelled child contributors are live after actual group registration.
Witness: a missing registered contributor has retired; its post-registration ancestry and
marker certificates would retire an uncancelled live producer owner, a contradiction.
-/
theorem State.UncancelledTaskAccounting.childGroupsPresent {queue : State}
    {work settled} (accounted : queue.UncancelledTaskAccounting settled)
    (priorStructural : queue.UncancelledRetiredAncestors work)
    (priorMarkers : queue.UncancelledRetiredMarkers work)
    (generated : ExecutedWork work) (taskMatching : queue.RegisteredTasksMatch work)
    (registration : queue.RegistrationFrame work) {parents : Nat → NodeRefs}
    (registry : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {producer : Task} (registered : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    : ∀ task ∈ result.work.tasks,
      ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ref ∉ (queue.addGroups result.work.groups).1.cancelledGroups
        → ref
          ∈ (queue.addGroups result.work.groups).1.groupNodes.map
              (fun node => node.group.node.ref) := by
  intro task member ref contributes uncancelled
  let grouped := (queue.addGroups result.work.groups).1
  have certificate := (registration.children producer registered).sourceChild rfl matching
  have descriptors : ∀ group ∈ result.work.groups, ∃ dependencies,
      GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head? := by
    intro group member
    obtain ⟨dependencies, known⟩ := matching.taskChildGroups_recordAt member
    exact ⟨dependencies, known,
      (matching.taskChildGroups_parentCanonical canonical member).trans
        (congrArg List.head? (canonical _ _ known)).symm⟩
  have structural := priorStructural.addGroups result.work.groups generated registration.live
    descriptors certificate.parentRefs
  have markers := priorMarkers.addGroups registry canonical result.work.groups generated
    registration.live descriptors certificate.parentRefs
  have installed := queue.addGroups_registration registration.live result.work.groups
  have refRegistered : ref ∈ grouped.registeredGroups := by
    rcases certificate.contributors task member ref contributes with old | candidate
    · exact installed.2.1 old
    · obtain ⟨group, included, same⟩ := candidate
      exact same ▸ installed.2.2 group included
  apply Classical.byContradiction
  intro absent
  have retired : grouped.RetiredGroup ref := ⟨refRegistered, absent⟩
  obtain ⟨node, dependencies, known, sameRef, owner, ownerMember, support⟩ :=
    matching.childContributor_producer_support generated member contributes
  obtain ⟨_, _, _, exactResult, _⟩ := matching
  have sameGroups : producer.groups = result.value.deliveryGroups :=
    Option.some.inj ((taskMatching producer registered).2.symm.trans exactResult)
  have producerContributes : owner ∈ producer.groups.map Execution.DeliveryNode.ref := by
    rw [sameGroups]; exact ownerMember
  obtain ⟨⟨_, payload, birth, _, producerKnown⟩, _⟩ := taskMatching producer registered
  have ownerRetired : grouped.RetiredGroup owner := by
    rcases support with same | ancestor
    · exact same ▸ retired
    · exact structural ref retired uncancelled node dependencies (groupRecordAt_of_nodeAt known)
        sameRef owner ancestor producer.occurrence _ ⟨birth, payload, producerKnown⟩ producerContributes
  have ownerUncancelled : owner ∉ queue.cancelledGroups := by
    have excluded : owner ∉ grouped.cancelledGroups := by
      rcases support with same | ancestor
      · exact same ▸ uncancelled
      · exact markers ref retired uncancelled node dependencies (groupRecordAt_of_nodeAt known)
          sameRef owner ancestor producer.occurrence _ ⟨birth, payload, producerKnown⟩ producerContributes
    exact fun member => excluded (queue.addGroups_cancelledGroups_subset result.work.groups member)
  obtain ⟨live, member, same, _⟩ :=
    accounted producer registered fresh owner producerContributes ownerUncancelled
  exact ownerRetired.2 (queue.addGroups_includesRefs result.work.groups owner
    (List.mem_map.mpr ⟨live, member, same⟩))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
