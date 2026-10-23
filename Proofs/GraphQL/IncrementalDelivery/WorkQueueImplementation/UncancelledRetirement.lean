import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementIntegration

/-! Structural ancestor closure for retirements not marked as cancelled. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Retirement structure can be separated from the accepted-failure inventory
-----------------------------------------------------------------------------------------

/-- Each permanently retired, uncancelled ref carries its full retirement certificate.
The certificate concerns task-bearing ancestors; the target may be a taskless record.
This proof-side invariant does not mention failures, output histories, or notice admission.
-/
def State.UncancelledRetiredAncestors (queue : State) (work : Execution.Work) : Prop :=
  ∀ ref,
    queue.RetiredGroup ref → ref ∉ queue.cancelledGroups → queue.AncestorsRetired work ref

/-- Uncancelled retirement supplies the earlier failure-indexed closure when cancellations
are supported. Witness: a healthy record cannot have a supported cancellation marker.
-/
theorem State.UncancelledRetiredAncestors.healthy {queue : State} {work failed}
    (prior : queue.UncancelledRetiredAncestors work)
    (supported : queue.CancelledRecordsSupported work failed)
    : queue.HealthyRetiredAncestors work failed := by
  intro ref retired healthy
  exact prior ref retired (supported.healthy_not_mem healthy)

/-- Before any failure, healthy-retirement closure supplies uncancelled closure as well.
Witness: invalidation has a failed contributing task, impossible in the empty inventory.
-/
theorem State.HealthyRetiredAncestors.uncancelled_of_empty {queue : State} {work}
    (prior : queue.HealthyRetiredAncestors work [])
    : queue.UncancelledRetiredAncestors work := by
  intro ref retired _
  exact prior ref retired (fun invalid => invalid.nonempty rfl)

/-- Generated initialization has structurally closed uncancelled retirement.
Witness: the checked empty-inventory initialization certificate includes taskless pruning.
-/
theorem ExecutedWork.initialUncancelledRetirement {work : Execution.Work}
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).UncancelledRetiredAncestors work :=
  generated.initialRetirement.2.uncancelled_of_empty

/-- Equal retirement sets and retained cancellation markers transport structural closure.
Witness: reflect the target retirement, exclude old cancellation, and carry all ancestors.
-/
theorem State.UncancelledRetiredAncestors.of_sameRetirements {before after : State} {work}
    (prior : before.UncancelledRetiredAncestors work)
    (same : ∀ ref, after.RetiredGroup ref ↔ before.RetiredGroup ref)
    (cancelled : before.cancelledGroups.Subset after.cancelledGroups)
    : after.UncancelledRetiredAncestors work := by
  intro ref retired uncancelled
  exact (prior ref ((same ref).mp retired)
    (fun member => uncancelled (cancelled member))).mono
    (fun ancestor retired => (same ancestor).mpr retired)

/-- Metadata replacement retains structural retirement closure.
Witness: the live-ref list, registry, and cancellation markers are unchanged.
-/
theorem State.UncancelledRetiredAncestors.putGroupNode {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (node : GroupNode)
    : (queue.putGroupNode node).UncancelledRetiredAncestors work := by
  apply prior.of_sameRetirements
  · intro ref
    simp only [State.RetiredGroup, State.putGroupNode_refs]
    rfl
  · exact fun _ member => member

/-- Task membership cleanup retains structural retirement closure.
Witness: mapped group records retain every ref and both permanent registries.
-/
theorem State.UncancelledRetiredAncestors.removeTask {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (occurrence : Occurrence)
    : (queue.removeTask occurrence).UncancelledRetiredAncestors work := by
  apply prior.of_sameRetirements
  · intro ref
    simp only [State.RetiredGroup, State.removeTask, List.map_map, Function.comp_def]
  · exact fun _ member => member

-----------------------------------------------------------------------------------------
-- Registration inherits uncancelled retirement from absent registered parents
-----------------------------------------------------------------------------------------

/-- A refused uncancelled child inherits its absent parent's ancestor certificate.
Witness: refusal below a cancelled parent would mark the child cancelled, so an
uncancelled refusal has an uncancelled, permanently retired parent.
-/
theorem State.UncancelledRetiredAncestors.addGroup {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (group : Group)
    (matching
      : ∃ dependencies,
          GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head?)
    (parentRegistered
      : ∀ parent, group.parent = some parent → parent ∈ queue.registeredGroups)
    : (queue.addGroup group).UncancelledRetiredAncestors work := by
  intro ref retired uncancelled
  rcases queue.addGroup_retired_origin group ref retired with old |
    ⟨same, fresh, parent, head, absent⟩
  · exact (prior ref old (fun member =>
      uncancelled (queue.addGroup_cancelledGroups_subset group member))).mono
        (fun _ ancestor => ancestor.addGroup group)
  subst ref
  have missing : queue.groupNode? group.node.ref = none := by
    apply (queue.groupNode?_eq_none_iff _).mpr
    intro live
    exact retired.2 (queue.addGroup_refs_subset group live)
  have parentUncancelled : parent ∉ queue.cancelledGroups := by
    intro marked
    apply uncancelled
    simp [State.addGroup, fresh, missing, head, absent, marked]
  have parentRetired : queue.RetiredGroup parent :=
    .of_lookup_none (parentRegistered parent head) absent
  obtain ⟨dependencies, known, canonical⟩ := matching
  have parentHead : dependencies.head? = some parent := canonical.symm.trans head
  cases dependencies with
  | nil => cases parentHead
  | cons first rest =>
      have equal : first = parent := Option.some.inj parentHead
      subst first
      obtain ⟨parentNode, parentRef, parentKnown⟩ := known.parent
      exact (State.AncestorsRetired.child generated known parentKnown
              (by simp [parentRef])
              (parentRef.symm ▸ prior parent parentRetired parentUncancelled)
              (parentRef.symm ▸ parentRetired)).mono
        (fun _ retired => retired.addGroup group)

/-- Parent-first registration preserves structural closure of uncancelled retirement.
Witness: execution-derived parent closure supplies registered parents at installation;
refused children inherit their certificates without introducing failure assumptions.
-/
theorem State.UncancelledRetiredAncestors.addGroups {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (groups : List Group)
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
    : (queue.addGroups groups).1.UncancelledRetiredAncestors work := by
  let property (current : State) := current.UncancelledRetiredAncestors work
    ∧ queue.registeredGroups ⊆ current.registeredGroups
  have ordered : ∀ group ∈ groups, ∀ parent, group.parent = some parent → parent < group.node.ref := by
    intro group member parent parentEq
    obtain ⟨dependencies, known, canonical⟩ := matching group member
    exact generated.groupRecordAncestorSmaller known
      (List.mem_of_head? (canonical.symm.trans parentEq))
  exact (State.addGroups_preserves_parentRegistered property groups ordered
    (fun current group member _ parents valid =>
      ⟨valid.1.addGroup generated group (matching group member) (fun parent parentEq =>
        (List.mem_append.mp (closed group member parent parentEq)).elim
          (fun known => valid.2 known) (parents parent parentEq)),
        valid.2.trans (current.addGroup_registeredGroups_subset_old group)⟩)
    queue coverage ⟨prior, List.Subset.refl _⟩).1

/-- Task installation preserves structural retirement closure.
Witness: membership updates retain old live refs and the registry, and never revive a ref.
-/
theorem State.UncancelledRetiredAncestors.addTask {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (task : Task)
    : (queue.addTask task).UncancelledRetiredAncestors work := by
  apply prior.of_sameRetirements
  · intro ref
    constructor
    · intro retired
      refine ⟨?_, fun live => retired.2 (queue.addTask_includesRefs task ref live)⟩
      have registered := retired.1
      rwa [queue.addTask_registeredGroups task] at registered
    · exact fun retired => retired.addTask task
  · rw [State.addTask_cancelledGroups]
    exact fun _ member => member

/-- Stream installation leaves all group retirement and cancellation data unchanged.
Witness: inspect the root and task-linked stream branches.
-/
theorem State.UncancelledRetiredAncestors.addStreams {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.UncancelledRetiredAncestors work := by
  unfold State.addStreams
  split
  · exact prior
  · dsimp
    split <;> exact prior

/-- Certified child-work registration preserves uncancelled retirement structure.
Witness: compose parent-first group registration with task and stream installation;
the declaration context is derived from execution and permanent task records.
-/
theorem State.UncancelledRetiredAncestors.maybeIntegrateWork {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (newWork : Work)
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
    : (queue.maybeIntegrateWork newWork parentTask).1.UncancelledRetiredAncestors
        work := by
  have loop (tasks : List Task) (current : State)
      (invariant : current.UncancelledRetiredAncestors work)
      : (tasks.foldl State.addTask current).UncancelledRetiredAncestors work := by
    induction tasks generalizing current with
    | nil => exact invariant
    | cons task rest ih => exact ih _ (invariant.addTask task)
  exact (loop newWork.tasks _
          (prior.addGroups newWork.groups generated coverage matching closed)).addStreams
    newWork.streams parentTask

/-- Failure removal preserves structural retirement closure, regardless of its target.
Witness: every newly absent ref is marked cancelled, so an uncancelled retirement was
already retired before removal. Existing ancestor retirements remain permanent.
-/
theorem State.UncancelledRetiredAncestors.removeGroup {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (root : Nat)
    : (queue.removeGroup root).UncancelledRetiredAncestors work := by
  intro ref retired uncancelled
  have old := queue.removeGroup_missing_uncancelled root ref retired.lookup_none uncancelled
  exact (prior ref (.of_lookup_none retired.1 old.1) old.2).mono
    (fun _ ancestor => ancestor.removeGroup root)

/-- Cache exposure preserves the retirement and cancellation records. -/
theorem State.UncancelledRetiredAncestors.cacheTaskFailures {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).UncancelledRetiredAncestors work := by
  apply prior.of_sameRetirements
  · intro ref
    simp only [State.RetiredGroup, State.cacheTaskFailures_registeredGroups,
      State.cacheTaskFailures_groupNodes]
  · rw [State.cacheTaskFailures_cancelledGroups]
    exact fun _ member => member

/-- Group startup creates no uncancelled retirement without an inherited certificate. -/
theorem State.UncancelledRetiredAncestors.startGroup {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.UncancelledRetiredAncestors work := by
  have cached := prior.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · have loop (tasks : List Occurrence) (current : State)
          (valid : current.UncancelledRetiredAncestors work)
          : (tasks.foldl (fun next task => next.startTask task available)
              current).UncancelledRetiredAncestors work := by
        induction tasks generalizing current with
        | nil => exact valid
        | cons task rest ih =>
            apply ih
            apply valid.of_sameRetirements
            · intro ref
              dsimp only
              unfold State.startTask
              split
              · rfl
              · split <;> rfl
            · dsimp only
              unfold State.startTask
              split
              · exact fun _ member => member
              · split <;> exact fun _ member => member
      exact loop _ _ cached
    · exact cached.removeGroup _

/-- Startup preserves structural retirement while marking immediately removed groups.
Previously retired ancestors remain retired throughout the group and stream folds.
-/
theorem State.UncancelledRetiredAncestors.startNewWork {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.UncancelledRetiredAncestors work := by
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (valid : acc.1.UncancelledRetiredAncestors work)
      : (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.UncancelledRetiredAncestors work := by
    induction refs generalizing acc with
    | nil => exact valid
    | cons ref rest ih => exact ih _ (valid.startGroup ref available)
  have streams (refs : NodeRefs) (current : State)
      (valid : current.UncancelledRetiredAncestors work)
      : (refs.foldl State.startStream current).UncancelledRetiredAncestors work := by
    induction refs generalizing current with
    | nil => exact valid
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact valid
  unfold State.startNewWork
  exact streams _ _ (loop _ _ prior)

-----------------------------------------------------------------------------------------
-- Successful pruning creates only protected retirements
-----------------------------------------------------------------------------------------

/-- Rejected task retention and owner removal preserve uncancelled retirements. -/
theorem State.UncancelledRetiredAncestors.taskFailure {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.UncancelledRetiredAncestors work := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using prior
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves
        (fun current => current.UncancelledRetiredAncestors work)
        (fun _ ref invariant => invariant.removeGroup ref) _ _ _ prior

/-- Filtering one protected parent preserves uncancelled ancestor closure.
Witness: the removed ref has its supplied certificate; every other newly absent ref was
already absent. Filtering retains all earlier ancestor retirements.
-/
theorem State.UncancelledRetiredAncestors.filter_parent {queue : State} {work ref}
    (prior : queue.UncancelledRetiredAncestors work)
    (protectedParent : queue.AncestorsRetired work ref)
    : ({
        queue with
          groupNodes := queue.groupNodes.filter (fun node => node.group.node.ref != ref)
      }).UncancelledRetiredAncestors
        work := by
  let next : State := { queue with
    groupNodes := queue.groupNodes.filter (fun node => node.group.node.ref != ref) }
  have preserves (ancestor) (retired : queue.RetiredGroup ancestor)
      : next.RetiredGroup ancestor := by
    refine ⟨retired.1, ?_⟩
    intro live
    obtain ⟨node, kept, same⟩ := List.mem_map.mp live
    exact retired.2 (List.mem_map.mpr ⟨node, (List.mem_filter.mp kept).1, same⟩)
  intro target retired uncancelled
  by_cases same : target = ref
  · subst target
    exact protectedParent.mono preserves
  · have old : queue.RetiredGroup target := by
      refine ⟨retired.1, ?_⟩
      intro live
      obtain ⟨node, member, nodeRef⟩ := List.mem_map.mp live
      exact retired.2 (List.mem_map.mpr ⟨node,
        List.mem_filter.mpr ⟨member, by simp [nodeRef, same]⟩, nodeRef⟩)
    exact (prior target old uncancelled).mono preserves

/-- Taskless pruning preserves uncancelled retirement and protects promoted groups.
Witness: the shared traversal applies the protected-parent filtering theorem at every
removal, propagating certificates down the generated chain.
-/
theorem State.UncancelledRetiredAncestors.pruneEmptyGroups {queue : State}
    {work parents} (prior : queue.UncancelledRetiredAncestors work)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (groups : List Execution.DeliveryNode)
    (protectedGroups : ∀ group ∈ groups, queue.AncestorsRetired work group.ref)
    : (queue.pruneEmptyGroups groups).1.UncancelledRetiredAncestors work :=
  (queue.pruneEmptyGroups_retirement_preserves generated matching links canonical
    registered groups protectedGroups
    (fun current => current.UncancelledRetiredAncestors work)
    (fun _ _ _ _ _ _ protectedParent invariant =>
      invariant.filter_parent protectedParent)).2
    prior

-----------------------------------------------------------------------------------------
-- Parent registration turns global structural closure into the missing-parent boundary
-----------------------------------------------------------------------------------------

/-- Closed uncancelled retirement supplies every accepting missing-parent certificate.
Witness: register the absent parent, recover its generated descriptor, and extend its
ancestor certificate to the live child. No failure-health premise enters this implication.
-/
theorem State.UncancelledRetiredAncestors.missingParent {queue : State} {work parents}
    (prior : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (parentFields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered
      : ∀ node ∈ queue.groupNodes,
          ∀ parent, node.group.parent = some parent → parent ∈ queue.registeredGroups)
    : queue.MissingParentAncestorsRetired work := by
  intro node member parent parentEq missing uncancelled
  have retired : queue.RetiredGroup parent :=
    .of_lookup_none (registered node member parent parentEq) missing
  obtain ⟨dependencies, known⟩ := matching node member
  have head : dependencies.head? = some parent := by
    rw [canonical _ _ known, ← parentFields node member, parentEq]
  cases dependencies with
  | nil => cases head
  | cons ref rest =>
      have same : ref = parent := Option.some.inj head
      subst ref
      obtain ⟨record, recordRef, parentKnown⟩ := known.parent
      exact State.AncestorsRetired.child generated known parentKnown
        (recordRef.symm ▸ head) (recordRef.symm ▸ prior parent retired uncancelled)
        (recordRef.symm ▸ retired)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
