import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedAncestry
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducerSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.GroupAccounting

/-! Retired ancestor certificates for successful release and task-child availability. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Only ancestors with actual contributing tasks need retirement evidence
-----------------------------------------------------------------------------------------

/-- Every task-bearing defer ancestor of the record `ref` is permanently retired.
The target may itself be a taskless ancestor record. Ancestors without contributing
tasks require no retirement evidence; the contributor witnesses remain static.
-/
def State.AncestorsRetired (queue : State) (work : Execution.Work) (ref : NodeRef)
    : Prop :=
  ∀ node dependencies,
    GroupRecordAt work node dependencies
    → node.ref = ref
    → ∀ ancestor ∈ dependencies,
        ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → ancestor ∈ owners
          → queue.RetiredGroup ancestor

/-- Every active root has permanently retired task-bearing ancestors.
This proof-side invariant says nothing about the root's own settlement or publication. -/
def State.RootAncestorsRetired (queue : State) (work : Execution.Work) : Prop :=
  ∀ ref ∈ queue.rootGroups, queue.AncestorsRetired work ref

/-- A healthy retired record's task-bearing ancestors have also retired.
Failure cleanup may retire unrelated invalidated shells, which are deliberately excluded.
This is a proof obligation for replay, not an additional source or conformance premise. -/
def State.HealthyRetiredAncestors (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ ref,
    queue.RetiredGroup ref
    → ¬GroupRecordInvalidated work failed ref
    → queue.AncestorsRetired work ref

/-- Ancestor certificates survive any transition that preserves permanent retirement.
Witness: transport each ancestor's existing registry-and-absence evidence. -/
theorem State.AncestorsRetired.mono {before after : State} {work ref}
    (ancestors : before.AncestorsRetired work ref)
    (preserved : ∀ ancestor, before.RetiredGroup ancestor → after.RetiredGroup ancestor)
    : after.AncestorsRetired work ref := by
  intro node dependencies known same ancestor member occurrence owners task contributes
  exact preserved ancestor (ancestors node dependencies known same ancestor member occurrence owners
    task contributes)

/-- Ancestor closure transports across a change with exactly the same retired refs.
Witness: reflect the target ref and transport each ancestor; no queue fields are added. -/
theorem State.HealthyRetiredAncestors.of_sameRetirements {before after : State}
    {work failed} (prior : before.HealthyRetiredAncestors work failed)
    (same : ∀ ref, after.RetiredGroup ref ↔ before.RetiredGroup ref)
    : after.HealthyRetiredAncestors work failed := by
  intro ref retired healthy
  exact (prior ref ((same ref).mp retired) healthy).mono
    (fun ancestor retired => (same ancestor).mpr retired)

/-- Adding failures weakens the healthy-retirement obligation.
Witness: a group healthy for the longer failure history was healthy for the shorter one. -/
theorem State.HealthyRetiredAncestors.mono_failures {queue : State}
    {work before after} (prior : queue.HealthyRetiredAncestors work before)
    (subset : before.Subset after)
    : queue.HealthyRetiredAncestors work after := by
  intro ref retired healthy
  exact prior ref retired (fun invalid => healthy (invalid.mono subset))

/-- Updating a live group's metadata preserves healthy-retirement closure.
Witness: replacement leaves registration history and live group refs unchanged. -/
theorem State.HealthyRetiredAncestors.putGroupNode {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (node : GroupNode)
    : (queue.putGroupNode node).HealthyRetiredAncestors work failed := by
  apply prior.of_sameRetirements
  intro ref
  simp only [State.RetiredGroup, State.putGroupNode_refs]
  rfl

/-- Removing task memberships does not itself retire any group.
Witness: the live-node map changes task lists only, so retirement is unchanged. -/
theorem State.HealthyRetiredAncestors.removeTask {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (occurrence : Occurrence)
    : (queue.removeTask occurrence).HealthyRetiredAncestors work failed := by
  apply prior.of_sameRetirements
  intro ref
  simp only [State.RetiredGroup, State.removeTask, List.map_map, Function.comp_def]

/-- One known record suffices to establish the certificate for a generated ref.
Witness: generated metadata gives every repeated record the same full ancestor list.
-/
theorem State.AncestorsRetired.of_record {queue : State}
    {work node dependencies} (generated : ExecutedWork work)
    (known : GroupRecordAt work node dependencies)
    (retired
      : ∀ ancestor ∈ dependencies,
          ∀ occurrence owners,
            TaskHasOwners work occurrence owners
            → ancestor ∈ owners
            → queue.RetiredGroup ancestor)
    : queue.AncestorsRetired work node.ref := by
  intro other otherDependencies descriptor same
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have equal : otherDependencies = dependencies := by
    rw [canonical _ _ descriptor, canonical _ _ known, same]
  simpa only [equal] using retired

/-- A contributing node's descriptor also establishes its record certificate.
Witness: every actual group node supplies a registration record with the same ancestry.
-/
theorem State.AncestorsRetired.of_descriptor {queue : State}
    {work node dependencies producer} (generated : ExecutedWork work)
    (known : NodeAt work node .group dependencies producer)
    (retired
      : ∀ ancestor ∈ dependencies,
          ∀ occurrence owners,
            TaskHasOwners work occurrence owners
            → ancestor ∈ owners
            → queue.RetiredGroup ancestor)
    : queue.AncestorsRetired work node.ref :=
  .of_record generated (groupRecordAt_of_nodeAt known) retired

/-- Retiring an immediate parent extends its ancestor certificate to the live child.
Witness: exact generated chains split the child's list into that parent and its full
ancestry. No assertion that the child has completed is needed. -/
theorem State.AncestorsRetired.child {queue : State}
    {work child dependencies parent parentDependencies}
    (generated : ExecutedWork work)
    (known : GroupRecordAt work child dependencies)
    (parentKnown : GroupRecordAt work parent parentDependencies)
    (head : dependencies.head? = some parent.ref)
    (ancestors : queue.AncestorsRetired work parent.ref)
    (retired : queue.RetiredGroup parent.ref)
    : queue.AncestorsRetired work child.ref := by
  apply State.AncestorsRetired.of_record generated known
  have chain := generated.groupRecordAncestryChain known parentKnown head
  intro ancestor member occurrence owners task contributes
  rw [chain] at member
  rcases List.mem_cons.mp member with same | earlier
  · exact same.symm ▸ retired
  · exact ancestors parent parentDependencies parentKnown rfl
      ancestor earlier occurrence owners task contributes

/-- Valid initialization requires no task-bearing ancestors of an announced root.
Witness: each initially satisfied dependency is protected against every possible failed
contributor, so the ancestor-retirement obligation is vacuous at this boundary. -/
theorem createWorkQueue_rootAncestorsRetired {work : Execution.Work}
    (generated : ExecutedWork work)
    (initialized
      : Initializes work (State.initialize (Work.fromExecution work)).initialGroups
          (State.initialize (Work.fromExecution work)).initialStreams)
    : (State.initialize (Work.fromExecution work)).RootAncestorsRetired work := by
  intro ref active
  rw [createWorkQueue_rootGroups] at active
  obtain ⟨node, member, same⟩ := List.mem_map.mp active
  obtain ⟨dependencies, producer, known, protection⟩ :=
    Initializes.groupDependencies_uninvalidated initialized member
  rw [← same]
  apply State.AncestorsRetired.of_descriptor generated known
  intro ancestor ancestorMember occurrence owners task contributes
  exact False.elim
    (protection [occurrence] ancestor ancestorMember (.task task contributes (by simp)))

-----------------------------------------------------------------------------------------
-- Empty-shell pruning installs retirement before promoting children
-----------------------------------------------------------------------------------------

/-- Filtering group records preserves every existing retirement certificate.
Witness: registration history is unchanged and filtering cannot introduce a live ref. -/
private theorem retired_filter {queue : State} {ref}
    (retired : queue.RetiredGroup ref) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep }).RetiredGroup ref := by
  refine ⟨retired.1, ?_⟩
  rintro member
  obtain ⟨node, included, same⟩ := List.mem_map.mp member
  exact retired.2 (List.mem_map.mpr ⟨node, (List.mem_filter.mp included).1, same⟩)

/-- Pruning protects promoted candidates and preserves a local retirement invariant.
Witness: the actual traversal retires each empty parent before examining its children;
exact parent chains extend that parent's certificate to live children. The callback
handles one protected record's removal, sharing the traversal proof across invariants.
-/
theorem State.pruneEmptyGroups_retirement_preserves {queue : State} {work parents}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (groups : List Execution.DeliveryNode)
    (protectedGroups : ∀ group ∈ groups, queue.AncestorsRetired work group.ref)
    (property : State → Prop)
    (preserved
      : ∀ current node,
          current.GroupNodesMatchWork work
          → current.ChildLinksCanonical parents
          → current.LiveGroupsRegistered
          → node ∈ current.groupNodes
          → current.AncestorsRetired work node.group.node.ref
          → property current
          → property
              {
                current with
                  groupNodes :=
                    current.groupNodes.filter
                      (fun entry => entry.group.node.ref != node.group.node.ref)
              })
    : (∀ group ∈ (queue.pruneEmptyGroups groups).2,
        (queue.pruneEmptyGroups groups).1.AncestorsRetired work group.ref)
      ∧ (property queue → property (queue.pruneEmptyGroups groups).1) := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (matched : current.GroupNodesMatchWork work)
      (linked : current.ChildLinksCanonical parents)
      (recorded : current.LiveGroupsRegistered)
      (pending : ∀ group ∈ remaining, current.AncestorsRetired work group.ref)
      (done : ∀ group ∈ kept, current.AncestorsRetired work group.ref)
      : (∀ group ∈ (State.pruneEmptyGroups.go fuel current remaining kept).2,
          (State.pruneEmptyGroups.go fuel current remaining kept).1.AncestorsRetired
            work group.ref)
        ∧ (property current →
          property (State.pruneEmptyGroups.go fuel current remaining kept).1) := by
    induction fuel generalizing current remaining kept with
    | zero => exact ⟨done, fun prior => prior⟩
    | succ fuel ih =>
        cases remaining with
        | nil => exact ⟨done, fun prior => prior⟩
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih current rest kept matched linked recorded
                (fun next member => pending next (List.mem_cons_of_mem _ member)) done
            · rename_i node found
              split
              · let next : State :=
                  { current with
                    groupNodes := current.groupNodes.filter
                      (fun entry => entry.group.node.ref != group.ref) }
                have preserve (ref) (retired : current.RetiredGroup ref)
                    : next.RetiredGroup ref := retired_filter retired _
                have nextMatching : next.GroupNodesMatchWork work :=
                  fun node member => matched node (List.mem_filter.mp member).1
                have nextLinks : next.ChildLinksCanonical parents :=
                  fun node member => linked node (List.mem_filter.mp member).1
                have nextRegistered : next.LiveGroupsRegistered :=
                  fun node member => recorded node (List.mem_filter.mp member).1
                have refEq := State.groupNode?_ref found
                have parentRetired : next.RetiredGroup group.ref := by
                  apply State.RetiredGroup.of_lookup_none
                  · exact refEq ▸ recorded node (List.mem_of_find?_eq_some found)
                  · change (current.groupNodes.filter
                      (fun node => node.group.node.ref != group.ref)).find?
                        (fun node => node.group.node.ref == group.ref) = none
                    apply List.find?_eq_none.mpr
                    intro node member
                    simpa using (List.mem_filter.mp member).2
                have parentProtected : next.AncestorsRetired work node.group.node.ref :=
                  refEq.symm ▸ (pending group List.mem_cons_self).mono preserve
                obtain ⟨dependencies, parentKnown⟩ :=
                  matched node (List.mem_of_find?_eq_some found)
                have nextProperty (prior : property current) : property next := by
                  have next := preserved current node matched linked recorded
                    (List.mem_of_find?_eq_some found)
                    (refEq.symm ▸ pending group List.mem_cons_self) prior
                  simpa only [refEq] using next
                have nextPending : ∀ candidate ∈
                    node.childGroups.filterMap
                      (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
                      ++ rest, next.AncestorsRetired work candidate.ref := by
                  intro candidate member
                  rcases List.mem_append.mp member with child | tail
                  · obtain ⟨ref, childMember, selected⟩ := List.mem_filterMap.mp child
                    cases childFound : current.groupNode? ref with
                    | none => simp [childFound] at selected
                    | some childNode =>
                        have same : childNode.group.node = candidate := by
                          simpa [childFound] using selected
                        obtain ⟨childDependencies, childKnown⟩ :=
                          matched childNode (List.mem_of_find?_eq_some childFound)
                        have head : childDependencies.head? = some node.group.node.ref := by
                          rw [canonical _ _ childKnown, State.groupNode?_ref childFound]
                          exact linked node (List.mem_of_find?_eq_some found) ref childMember
                        have protection := State.AncestorsRetired.child generated childKnown
                          parentKnown head parentProtected (refEq.symm ▸ parentRetired)
                        exact same ▸ protection
                  · exact (pending candidate (List.mem_cons_of_mem _ tail)).mono preserve
                have final := ih next _ kept nextMatching nextLinks nextRegistered nextPending
                  (fun group member => (done group member).mono preserve)
                exact ⟨final.1, fun prior => final.2 (nextProperty prior)⟩
              · apply ih current rest (kept ++ [group]) matched linked recorded
                  (fun next member => pending next (List.mem_cons_of_mem _ member))
                intro next member
                rcases List.mem_append.mp member with earlier | latest
                · exact done next earlier
                · have same := List.mem_singleton.mp latest
                  exact same ▸ pending group List.mem_cons_self
  exact loop _ queue groups [] matching links registered protectedGroups
    (by intro group member; cases member)

/-- Pruning preserves healthy-retirement closure while protecting promoted candidates.
Witness: instantiate the shared traversal theorem; the only newly retired ref is the
protected parent being removed, and earlier ancestor retirements persist under filtering.
-/
theorem State.pruneEmptyGroups_retirement {queue : State} {work parents failed}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (groups : List Execution.DeliveryNode)
    (protectedGroups : ∀ group ∈ groups, queue.AncestorsRetired work group.ref)
    : (∀ group ∈ (queue.pruneEmptyGroups groups).2,
        (queue.pruneEmptyGroups groups).1.AncestorsRetired work group.ref)
      ∧ (queue.HealthyRetiredAncestors work failed
          → (queue.pruneEmptyGroups groups).1.HealthyRetiredAncestors work failed) := by
  apply queue.pruneEmptyGroups_retirement_preserves generated matching links canonical
    registered groups protectedGroups
    (fun current => current.HealthyRetiredAncestors work failed)
  intro current node _ _ _ _ protectedParent prior ref retired healthy
  have preserves (ref) (old : current.RetiredGroup ref)
      : ({ current with
          groupNodes := current.groupNodes.filter
            (fun entry => entry.group.node.ref != node.group.node.ref) }).RetiredGroup ref :=
    retired_filter old _
  by_cases same : ref = node.group.node.ref
  · exact same ▸ protectedParent.mono preserves
  · have old : current.RetiredGroup ref := by
      refine ⟨retired.1, ?_⟩
      intro member
      obtain ⟨entry, entryMember, entryRef⟩ := List.mem_map.mp member
      exact retired.2 (List.mem_map.mpr ⟨entry, List.mem_filter.mpr
        ⟨entryMember, by simp [entryRef, same]⟩, entryRef⟩)
    exact (prior ref old healthy).mono preserves

/-- Every group promoted by pruning retains its retired task-bearing ancestors.
Witness: the candidate projection of the joint pruning preservation theorem. -/
theorem State.pruneEmptyGroups_ancestorsRetired {queue : State} {work parents}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (groups : List Execution.DeliveryNode)
    (protectedGroups : ∀ group ∈ groups, queue.AncestorsRetired work group.ref)
    : ∀ group ∈ (queue.pruneEmptyGroups groups).2,
        (queue.pruneEmptyGroups groups).1.AncestorsRetired work group.ref :=
  (State.pruneEmptyGroups_retirement (failed := []) generated matching links canonical
    registered groups protectedGroups).1

/-- Successful closure retires the completed group and protects every promoted child's
task-bearing ancestors. Witness: flushing preserves metadata and the registry; closure
retires the parent; exact parent chains and the pruning theorem establish child
certificates. This also retains the completed group's own ancestor certificate. -/
theorem State.finishGroupSuccess_retirement {queue : State} {work parents failed}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) {group : GroupNode}
    (member : group ∈ queue.groupNodes)
    (protectedGroup : queue.AncestorsRetired work group.group.node.ref)
    : let next := queue.finishGroupSuccess group
      next.1.RetiredGroup group.group.node.ref
      ∧ next.1.AncestorsRetired work group.group.node.ref
      ∧ (∀ child ∈ next.2.2.newGroups, next.1.AncestorsRetired work child.ref)
      ∧ (queue.HealthyRetiredAncestors work failed
          → next.1.HealthyRetiredAncestors work failed) := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  let property (current : State) := current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents ∧ current.LiveGroupsRegistered
    ∧ current.registeredGroups = queue.registeredGroups
    ∧ current.AncestorsRetired work group.group.node.ref
    ∧ (queue.HealthyRetiredAncestors work failed →
      current.HealthyRetiredAncestors work failed)
  have loop (more : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (prior : property acc.1) : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons occurrence rest ih =>
        apply ih
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact prior
        · refine ⟨prior.1.removeTask occurrence, prior.2.1.removeTask occurrence, ?_,
            prior.2.2.2.1,
            prior.2.2.2.2.1.mono (fun ref retired => retired.removeTask occurrence),
            fun closure => (prior.2.2.2.2.2 closure).removeTask occurrence⟩
          intro node nodeMember
          obtain ⟨old, oldMember, same⟩ := List.mem_map.mp nodeMember
          subst node
          exact prior.2.2.1 old oldMember
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedFacts : property flushed := loop group.tasks (queue, [], [])
    ⟨matching, links, registered, rfl, protectedGroup, fun closure => closure⟩
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have preserves (ref) (retired : flushed.RetiredGroup ref) : current.RetiredGroup ref :=
    retired_filter retired _
  have currentMatching : current.GroupNodesMatchWork work :=
    fun node member => flushedFacts.1 node (List.mem_filter.mp member).1
  have currentLinks : current.ChildLinksCanonical parents :=
    fun node member => flushedFacts.2.1 node (List.mem_filter.mp member).1
  have currentRegistered : current.LiveGroupsRegistered :=
    fun node member => flushedFacts.2.2.1 node (List.mem_filter.mp member).1
  have parentRetired : current.RetiredGroup group.group.node.ref := by
    apply State.RetiredGroup.of_lookup_none
    · change group.group.node.ref ∈ flushed.registeredGroups
      rw [flushedFacts.2.2.2.1]
      exact registered group member
    · change (flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)).find?
          (fun node => node.group.node.ref == group.group.node.ref) = none
      apply List.find?_eq_none.mpr
      intro node member
      simpa using (List.mem_filter.mp member).2
  have parentProtected : current.AncestorsRetired work group.group.node.ref :=
    flushedFacts.2.2.2.2.1.mono preserves
  have currentClosure (prior : queue.HealthyRetiredAncestors work failed)
      : current.HealthyRetiredAncestors work failed := by
    intro ref retired healthy
    by_cases same : ref = group.group.node.ref
    · exact same ▸ parentProtected
    · have old : flushed.RetiredGroup ref := by
        refine ⟨retired.1, ?_⟩
        intro member
        obtain ⟨entry, entryMember, entryRef⟩ := List.mem_map.mp member
        exact retired.2 (List.mem_map.mpr ⟨entry, List.mem_filter.mpr
          ⟨entryMember, by simp [entryRef, same]⟩, entryRef⟩)
      exact (flushedFacts.2.2.2.2.2 prior ref old healthy).mono preserves
  obtain ⟨dependencies, parentKnown⟩ := matching group member
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  have childProtected : ∀ child ∈ children, current.AncestorsRetired work child.ref := by
    intro child childMember
    obtain ⟨ref, linked, selected⟩ := List.mem_filterMap.mp childMember
    cases found : current.groupNode? ref with
    | none => simp [found] at selected
    | some node =>
        have same : node.group.node = child := by simpa [found] using selected
        obtain ⟨childDependencies, childKnown⟩ :=
          currentMatching node (List.mem_of_find?_eq_some found)
        have head : childDependencies.head? = some group.group.node.ref := by
          rw [canonical _ _ childKnown, State.groupNode?_ref found]
          exact links group member ref linked
        exact same ▸ State.AncestorsRetired.child generated childKnown parentKnown head
          parentProtected parentRetired
  have pruned := State.pruneEmptyGroups_retirement (failed := failed) generated
    currentMatching currentLinks
    canonical currentRegistered children childProtected
  refine ⟨parentRetired.pruneEmptyGroups children, ?_, pruned.1, ?_⟩
  · exact protectedGroup.mono (fun ref retired => retired.finishGroupSuccess group)
  · exact fun prior => pruned.2 (currentClosure prior)

/-- Successful closure protects the completed parent and all promoted children.
Witness: project the certificates from joint closure/pruning preservation. -/
theorem State.finishGroupSuccess_ancestorsRetired {queue : State} {work parents}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) {group : GroupNode}
    (member : group ∈ queue.groupNodes)
    (protectedGroup : queue.AncestorsRetired work group.group.node.ref)
    : let next := queue.finishGroupSuccess group
      next.1.RetiredGroup group.group.node.ref
      ∧ next.1.AncestorsRetired work group.group.node.ref
      ∧ ∀ child ∈ next.2.2.newGroups, next.1.AncestorsRetired work child.ref := by
  have result := State.finishGroupSuccess_retirement (failed := []) generated matching links
    canonical registered member protectedGroup
  exact ⟨result.1, result.2.1, result.2.2.1⟩

-----------------------------------------------------------------------------------------
-- The actual single-pass success loop retains completed-ancestor protection
-----------------------------------------------------------------------------------------

/-- Transport active-root certificates when roots only shrink and retirement persists.
Witness: reuse each old root certificate and preserve its retired ancestors. -/
theorem State.RootAncestorsRetired.mono {before after : State} {work}
    (roots : before.RootAncestorsRetired work)
    (subset : after.rootGroups.Subset before.rootGroups)
    (preserved : ∀ ref, before.RetiredGroup ref → after.RetiredGroup ref)
    : after.RootAncestorsRetired work := by
  intro ref active
  exact (roots ref (subset active)).mono preserved

/-- The contributor loop preserves old roots' ancestor certificates and records them
for all newly released groups. Witness: pending updates preserve retirement; successful
closure supplies the new certificates; later iterations retain earlier releases. -/
theorem successGroupFold_retirement {queue : State} {work parents failed}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (protectedRoots : queue.RootAncestorsRetired work)
    (groups : List Execution.DeliveryNode)
    : let result := groups.foldl successGroupStep (queue, [], {})
      result.1.RootAncestorsRetired work
      ∧ (∀ node ∈ result.2.2.newGroups, result.1.AncestorsRetired work node.ref)
      ∧ (queue.HealthyRetiredAncestors work failed
          → result.1.HealthyRetiredAncestors work failed) := by
  let property (acc : State × List WorkQueueEvent × NewWork) :=
    acc.1.GroupNodesMatchWork work ∧ acc.1.ChildLinksCanonical parents
    ∧ acc.1.LiveGroupsRegistered ∧ acc.1.TaskGroupsRegistered
    ∧ acc.1.RootAncestorsRetired work
    ∧ (∀ node ∈ acc.2.2.newGroups, acc.1.AncestorsRetired work node.ref)
    ∧ (queue.HealthyRetiredAncestors work failed →
      acc.1.HealthyRetiredAncestors work failed)
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (prior : property acc) : property (successGroupStep acc group) := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact prior
    · rename_i node found
      let updated := { node with pending := node.pending - 1 }
      let next := current.putGroupNode updated
      have oldMember := List.mem_of_find?_eq_some found
      have nextMatching : next.GroupNodesMatchWork work :=
        prior.1.putGroupNode updated (prior.1 node oldMember)
      have nextLinks : next.ChildLinksCanonical parents :=
        prior.2.1.putGroupNode updated (prior.2.1 node oldMember)
      have nextRegistered : next.LiveGroupsRegistered :=
        prior.2.2.1.putGroupNode updated (prior.2.2.1 node oldMember)
      have nextTasks : next.TaskGroupsRegistered := prior.2.2.2.1
      have preserve (ref) (retired : current.RetiredGroup ref) : next.RetiredGroup ref :=
        retired.putGroupNode updated
      have nextRoots : next.RootAncestorsRetired work :=
        prior.2.2.2.2.1.mono (fun _ member => member) preserve
      split
      · rename_i finishes
        have active : node.group.node.ref ∈ next.rootGroups := by
          have flags := Bool.and_eq_true_iff.mp finishes
          have refEq := State.groupNode?_ref found
          simpa only [refEq, List.contains_iff_mem]
            using (Bool.and_eq_true_iff.mp flags.1).1
        have updatedMember : updated ∈ next.groupNodes := by
          apply List.mem_map.mpr
          exact ⟨node, oldMember, by simp [updated]⟩
        have closed := State.finishGroupSuccess_retirement (failed := failed)
          generated nextMatching
          nextLinks canonical nextRegistered updatedMember (nextRoots _ active)
        have registration := State.finishGroupSuccess_registration nextRegistered nextTasks updated
        refine ⟨
          nextMatching.finishGroupSuccess updated,
          nextLinks.finishGroupSuccess updated,
          registration.1,
          registration.2.1,
          nextRoots.mono (next.finishGroupSuccess_rootsSubset updated)
            (fun ref retired => retired.finishGroupSuccess updated),
          ?_,
          ?_
        ⟩
        · intro candidate member
          rcases List.mem_append.mp member with earlier | new
          · exact (prior.2.2.2.2.2.1 candidate earlier).mono
              (fun ref retired => (preserve ref retired).finishGroupSuccess updated)
          · exact closed.2.2.1 candidate new
        · exact fun closure => closed.2.2.2
            ((prior.2.2.2.2.2.2 closure).putGroupNode updated)
      · exact ⟨nextMatching, nextLinks, nextRegistered, nextTasks, nextRoots,
          fun candidate member => (prior.2.2.2.2.2.1 candidate member).mono preserve,
          fun closure => (prior.2.2.2.2.2.2 closure).putGroupNode updated⟩
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (prior : property acc) : property (more.foldl successGroupStep acc) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons group rest ih => exact ih _ (step acc group prior)
  exact (loop groups (queue, [], {})
          ⟨
            matching,
            links,
            registered,
            tasks,
            protectedRoots,
            by simp,
            fun closure => closure
          ⟩).2.2.2.2

/-- The single-pass contributor loop protects old roots and new releases.
Witness: project the root and release certificates from joint retirement preservation. -/
theorem successGroupFold_ancestorsRetired {queue : State} {work parents}
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (protectedRoots : queue.RootAncestorsRetired work)
    (groups : List Execution.DeliveryNode)
    : let result := groups.foldl successGroupStep (queue, [], {})
      result.1.RootAncestorsRetired work
      ∧ ∀ node ∈ result.2.2.newGroups, result.1.AncestorsRetired work node.ref := by
  have result := successGroupFold_retirement (failed := []) generated matching links
    canonical registered tasks protectedRoots groups
  exact ⟨result.1, result.2.1⟩

-----------------------------------------------------------------------------------------
-- Retirement and the existing task ledger exclude a new ancestor failure
-----------------------------------------------------------------------------------------

/-- A healthy retired contributor can only belong to already-settled registered tasks.
Witness: otherwise the existing task ledger supplies a live group, contradicting
permanent retirement. This does not yet cover tasks revealed by future integration. -/
theorem State.HealthyRegisteredTaskAccounting.retired_contributor_settled
    {queue : State} {work settled failed}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (registered : task ∈ queue.tasks) {ref}
    (contributes : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (healthy : ¬GroupInvalidated work failed ref) (retired : queue.RetiredGroup ref)
    : task.occurrence ∈ settled := by
  apply Classical.byContradiction
  intro fresh
  obtain ⟨node, member, same, _⟩ :=
    accounted task registered fresh ref contributes healthy
  exact retired.2 (List.mem_map.mpr ⟨node, member, same⟩)

-----------------------------------------------------------------------------------------
-- The same completed-ancestor invariant resolves task-success registration reuse
-----------------------------------------------------------------------------------------

/-- A newly revealed healthy group is available if healthy retirement is ancestor-closed.
Witness: an unavailable candidate has a live pending producer ancestor. Its retirement
certificate would require that same ancestor to be retired, a contradiction. This
discharges the reuse case without treating settlement as publication. -/
theorem State.HealthyRetiredAncestors.childGroup_available
    {queue : State} {work settled failed}
    (retirement : queue.HealthyRetiredAncestors work failed)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    {producer : Task} (registered : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    {group : Group} (member : group ∈ result.work.groups)
    (contributing
      : ∃ task ∈ result.work.tasks,
          group.node.ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (healthy : ¬GroupInvalidated work failed group.node.ref)
    : queue.GroupAvailable group.node.ref := by
  apply Classical.byContradiction
  intro unavailable
  have retired := (queue.groupUnavailable_iff_retired group.node.ref).mp unavailable
  obtain ⟨dependencies, known, node, nodeMember, _, owner, _, _, ancestor, _⟩ :=
    accounted.unavailable_child_live_ancestor tracks taskMatching generated registered fresh
      matching member contributing healthy unavailable
  have protectedGroup := retirement group.node.ref retired
    (fun invalid => healthy
      ((generated.groupRecordInvalidated_iff_groupInvalidated known).mp invalid))
  obtain ⟨⟨address, payload, birth, _, producerKnown⟩, _⟩ := taskMatching producer registered
  have impossible := protectedGroup group.node dependencies (groupRecordAt_of_nodeAt known) rfl
    node.group.node.ref ancestor producer.occurrence _ ⟨birth, payload, producerKnown⟩ owner
  exact impossible.2 (List.mem_map_of_mem nodeMember)

/-- Ancestor-closed healthy retirement supplies all registration availability for a
matching task success. Witness: each new task contributor appears among the same chunk's
candidate groups, to which the live-producer contradiction applies. -/
theorem State.HealthyRetiredAncestors.childGroupsAvailable
    {queue : State} {work settled failed}
    (retirement : queue.HealthyRetiredAncestors work failed)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    {producer : Task} (registered : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    : queue.ChildGroupsAvailable work failed result.work := by
  intro task member ref contributes healthy
  obtain ⟨group, candidate, same⟩ := matching.childTasksCovered task member ref contributes
  rw [← same] at healthy ⊢
  exact retirement.childGroup_available accounted tracks taskMatching generated
    registered fresh matching candidate ⟨task, member, same.symm ▸ contributes⟩ healthy

/-- Starting work preserves healthy-retirement closure.
Witness: activation leaves both registration history and the live group map unchanged. -/
theorem State.HealthyRetiredAncestors.startNewWork {queue : State} {work failed}
    (prior : queue.HealthyRetiredAncestors work failed) (newWork : NewWork)
    : (queue.startNewWork newWork).HealthyRetiredAncestors work failed := by
  apply prior.of_sameRetirements
  intro ref
  simp only [State.RetiredGroup, queue.startNewWork_registeredGroups,
    (queue.startNewWork_groupCore newWork).1]

/-- Removing an invalidated subtree preserves healthy-retirement closure.
Witness: every healthy live node is retained by cleanup, so every healthy retired ref
was already retired. Its ancestors stay retired throughout removal. -/
theorem State.HealthyRetiredAncestors.removeGroup {queue : State} {work failed parents}
    (prior : queue.HealthyRetiredAncestors work failed)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : NodeRef) (invalid : GroupRecordInvalidated work failed ref)
    : (queue.removeGroup ref).HealthyRetiredAncestors work failed := by
  intro target retired healthy
  have old : queue.RetiredGroup target := by
    refine ⟨retired.1, ?_⟩
    intro live
    obtain ⟨node, member, same⟩ := List.mem_map.mp live
    have retained := State.removeGroup_recordHealthyRetained links matching canonical ref invalid
      node member (same.symm ▸ healthy)
    exact retired.2 (List.mem_map.mpr ⟨node, retained, same⟩)
  exact (prior target old healthy).mono (fun ancestor retired => retired.removeGroup ref)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
