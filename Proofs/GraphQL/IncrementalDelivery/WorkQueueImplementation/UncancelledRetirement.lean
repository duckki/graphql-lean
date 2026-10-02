import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementIntegration

/-! Structural ancestor closure for retirements not marked as cancelled. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Retirement structure can be separated from the accepted-failure inventory
-----------------------------------------------------------------------------------------

/-- Each permanently retired, uncancelled key carries its full retirement certificate.
The certificate concerns task-bearing ancestors; the target may be a taskless record.
This proof-side invariant does not mention failures, output histories, or notice admission.
-/
def State.UncancelledRetiredAncestors (queue : State) (work : Execution.Work) : Prop :=
  ∀ key,
    queue.RetiredGroup key → key ∉ queue.cancelledGroups → queue.AncestorsRetired work key

/-- Uncancelled retirement supplies the earlier failure-indexed closure when cancellations
are supported. Witness: a healthy record cannot have a supported cancellation marker.
-/
theorem State.UncancelledRetiredAncestors.healthy {queue : State} {work failed}
    (prior : queue.UncancelledRetiredAncestors work)
    (supported : queue.CancelledRecordsSupported work failed)
    : queue.HealthyRetiredAncestors work failed := by
  intro key retired healthy
  exact prior key retired (supported.healthy_not_mem healthy)

/-- Before any failure, healthy-retirement closure supplies uncancelled closure as well.
Witness: invalidation has a failed contributing task, impossible in the empty inventory.
-/
theorem State.HealthyRetiredAncestors.uncancelled_of_empty {queue : State} {work}
    (prior : queue.HealthyRetiredAncestors work [])
    : queue.UncancelledRetiredAncestors work := by
  intro key retired _
  exact prior key retired (fun invalid => invalid.nonempty rfl)

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
    (same : ∀ key, after.RetiredGroup key ↔ before.RetiredGroup key)
    (cancelled : before.cancelledGroups.Subset after.cancelledGroups)
    : after.UncancelledRetiredAncestors work := by
  intro key retired uncancelled
  exact (prior key ((same key).mp retired)
    (fun member => uncancelled (cancelled member))).mono
    (fun ancestor retired => (same ancestor).mpr retired)

/-- Metadata replacement retains structural retirement closure.
Witness: the live-key list, registry, and cancellation markers are unchanged.
-/
theorem State.UncancelledRetiredAncestors.putGroupNode {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (node : GroupNode)
    : (queue.putGroupNode node).UncancelledRetiredAncestors work := by
  apply prior.of_sameRetirements
  · intro key
    simp only [State.RetiredGroup, State.putGroupNode_keys]
    rfl
  · exact fun _ member => member

/-- Task membership cleanup retains structural retirement closure.
Witness: mapped group records retain every key and both permanent registries.
-/
theorem State.UncancelledRetiredAncestors.removeTask {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (occurrence : Occurrence)
    : (queue.removeTask occurrence).UncancelledRetiredAncestors work := by
  apply prior.of_sameRetirements
  · intro key
    simp only [State.RetiredGroup, State.removeTask, List.map_map, Function.comp_def]
  · exact fun _ member => member

/-- Starting released work changes neither retirement nor cancellation data.
Witness: activation's exact live-group and registry equations transport the invariant.
-/
theorem State.UncancelledRetiredAncestors.startNewWork {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (released : NewWork)
    : (queue.startNewWork released).UncancelledRetiredAncestors work := by
  apply prior.of_sameRetirements
  · intro key
    simp only [State.RetiredGroup, State.startNewWork_registeredGroups,
      (queue.startNewWork_groupCore released).1]
  · rw [State.startNewWork_cancelledGroups]
    exact fun _ member => member

-----------------------------------------------------------------------------------------
-- Registration and cancellation create no new uncancelled retirements
-----------------------------------------------------------------------------------------

/-- Group registration preserves structural retirement closure without failure support.
Witness: a newly retired registration is marked cancelled; all other retirements and
their ancestor certificates come from the original queue.
-/
theorem State.UncancelledRetiredAncestors.addGroups {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (groups : List Group)
    : (queue.addGroups groups).1.UncancelledRetiredAncestors work := by
  intro key retired uncancelled
  have old := (queue.addGroups_retired_or_cancelled groups key retired).resolve_right
    uncancelled
  have notCancelled : key ∉ queue.cancelledGroups :=
    fun member => uncancelled (queue.addGroups_cancelledGroups_subset groups member)
  exact (prior key old notCancelled).mono (fun _ ancestor => ancestor.addGroups groups)

/-- Task installation preserves structural retirement closure.
Witness: membership updates retain old live keys and the registry, and never revive a key.
-/
theorem State.UncancelledRetiredAncestors.addTask {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (task : Task)
    : (queue.addTask task).UncancelledRetiredAncestors work := by
  apply prior.of_sameRetirements
  · intro key
    constructor
    · intro retired
      refine ⟨?_, fun live => retired.2 (queue.addTask_includesKeys task key live)⟩
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

/-- Arbitrary child-work registration preserves uncancelled retirement structure.
Witness: compose group registration with task and stream installation. In particular,
this needs no generated-work, health, pending-owner, or cancellation-support premise.
-/
theorem State.UncancelledRetiredAncestors.maybeIntegrateWork {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (newWork : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.UncancelledRetiredAncestors
        work := by
  have loop (tasks : List Task) (current : State)
      (invariant : current.UncancelledRetiredAncestors work)
      : (tasks.foldl State.addTask current).UncancelledRetiredAncestors work := by
    induction tasks generalizing current with
    | nil => exact invariant
    | cons task rest ih => exact ih _ (invariant.addTask task)
  exact (loop newWork.tasks _ (prior.addGroups newWork.groups)).addStreams
    newWork.streams parentTask

/-- Failure removal preserves structural retirement closure, regardless of its target.
Witness: every newly absent key is marked cancelled, so an uncancelled retirement was
already retired before removal. Existing ancestor retirements remain permanent.
-/
theorem State.UncancelledRetiredAncestors.removeGroup {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (root : Nat)
    : (queue.removeGroup root).UncancelledRetiredAncestors work := by
  intro key retired uncancelled
  have old := queue.removeGroup_missing_uncancelled root key retired.lookup_none uncancelled
  exact (prior key (.of_lookup_none retired.1 old.1) old.2).mono
    (fun _ ancestor => ancestor.removeGroup root)

-----------------------------------------------------------------------------------------
-- Successful pruning creates only protected retirements
-----------------------------------------------------------------------------------------

/-- Filtering one protected parent preserves uncancelled ancestor closure.
Witness: the removed key has its supplied certificate; every other newly absent key was
already absent. Filtering retains all earlier ancestor retirements.
-/
theorem State.UncancelledRetiredAncestors.filter_parent {queue : State} {work key}
    (prior : queue.UncancelledRetiredAncestors work)
    (protectedParent : queue.AncestorsRetired work key)
    : ({
        queue with
          groupNodes := queue.groupNodes.filter (fun node => node.group.node.key != key)
      }).UncancelledRetiredAncestors
        work := by
  let next : State := { queue with
    groupNodes := queue.groupNodes.filter (fun node => node.group.node.key != key) }
  have preserves (ancestor) (retired : queue.RetiredGroup ancestor)
      : next.RetiredGroup ancestor := by
    refine ⟨retired.1, ?_⟩
    intro live
    obtain ⟨node, kept, same⟩ := List.mem_map.mp live
    exact retired.2 (List.mem_map.mpr ⟨node, (List.mem_filter.mp kept).1, same⟩)
  intro target retired uncancelled
  by_cases same : target = key
  · subst target
    exact protectedParent.mono preserves
  · have old : queue.RetiredGroup target := by
      refine ⟨retired.1, ?_⟩
      intro live
      obtain ⟨node, member, nodeKey⟩ := List.mem_map.mp live
      exact retired.2 (List.mem_map.mpr ⟨node,
        List.mem_filter.mpr ⟨member, by simp [nodeKey, same]⟩, nodeKey⟩)
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
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (registered : queue.LiveGroupsRegistered) (groups : List Execution.DeliveryNode)
    (protectedGroups : ∀ group ∈ groups, queue.AncestorsRetired work group.key)
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
          GroupRecordAt work node dependencies → dependencies = parents node.key)
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
  | cons key rest =>
      have same : key = parent := Option.some.inj head
      subst key
      obtain ⟨record, recordKey, parentKnown⟩ := known.parent
      exact State.AncestorsRetired.child generated known parentKnown
        (recordKey.symm ▸ head) (recordKey.symm ▸ prior parent retired uncancelled)
        (recordKey.symm ▸ retired)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
