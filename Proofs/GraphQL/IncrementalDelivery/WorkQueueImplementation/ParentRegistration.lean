import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupParents

/-! Declaration-context lowering and permanent registration of primary parents. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every lowered parent has a prior or current registration
-----------------------------------------------------------------------------------------

/-- Each primary parent is already known or has a candidate in this work chunk.
The parent need not contribute to any task or remain live after integration.
-/
def Work.ParentsCovered (work : Work) (known : NodeRefs := []) : Prop :=
  ∀ group ∈ work.groups,
    ∀ parent,
      group.parent = some parent
      → parent ∈ known ∨ ∃ candidate ∈ work.groups, candidate.node.ref = parent

/-- Prior registration contexts can grow without invalidating parent coverage. -/
theorem Work.ParentsCovered.mono {work : Work} {known more : NodeRefs}
    (covered : work.ParentsCovered known) (included : known.Subset more)
    : work.ParentsCovered more := by
  intro group member parent same
  rcases covered group member parent same with prior | candidate
  · exact .inl (included prior)
  · exact .inr candidate

/-- Execution declaration contexts cover every primary parent of a lowered candidate. -/
theorem workFromSpec_parentsCovered (work : Execution.Work)
    (certified : DeclarationCoverage.Certified [] work) (address : Address := [])
    : (Work.fromExecution work address).ParentsCovered := by
  intro group member parent same
  have covered := certified.parents address member same
  exact Or.inr (List.mem_map.mp ((List.mem_append.mp covered).resolve_left (by simp)))

/-- A producer's inherited context covers primary parents of its child declarations. -/
theorem GraphEvent.MatchesWork.childParentsCovered
    {work occurrence result known task}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (context : DeclarationCoverage.TaskChildrenCertified work known task)
    (same : task.occurrence = occurrence)
    : result.work.ParentsCovered known :=
  (context.sourceChild same matching).parents

/-- Stream item declarations restart the context and cover all parents within the item. -/
theorem GraphEvent.MatchesWork.streamItem_parentsCovered
    {work stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (certified : DeclarationCoverage.Certified [] work)
    {item : StreamItem} (member : item ∈ items)
    : item.work.ParentsCovered :=
  (certified.sourceStreamItem matching member []).parents

-----------------------------------------------------------------------------------------
-- The permanent registry is closed under the generated primary-parent assignment
-----------------------------------------------------------------------------------------

/-- Every registered ref's assigned primary parent is permanently registered as well.
This structural property concerns the registry, not live nodes, failure health, or notices.
-/
def State.ParentRegistryClosed (queue : State) (parents : Nat → NodeRefs) : Prop :=
  ∀ ref ∈ queue.registeredGroups,
    ∀ parent, (parents ref).head? = some parent → parent ∈ queue.registeredGroups

/-- Equal registries transport primary-parent closure across arbitrary metadata changes.
Witness: rewrite membership on both sides with the supplied registry equality.
-/
theorem State.ParentRegistryClosed.of_sameRegistry {before after : State} {parents}
    (prior : before.ParentRegistryClosed parents)
    (same : after.registeredGroups = before.registeredGroups)
    : after.ParentRegistryClosed parents := by
  simpa only [State.ParentRegistryClosed, same] using prior

/-- Registering a complete candidate batch preserves primary-parent registry closure.
Witness: an old ref uses prior closure; a new ref's canonical parent occurs in the same
batch and is registered even when its live shell is absent or registration is reused.
-/
theorem State.ParentRegistryClosed.addGroups {queue : State} {parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (groups : List Group)
    (canonical : ∀ group ∈ groups, group.parent = (parents group.node.ref).head?)
    (covered
      : ∀ group ∈ groups,
          ∀ parent,
            group.parent = some parent
            → parent ∈ queue.registeredGroups
              ∨ ∃ candidate ∈ groups, candidate.node.ref = parent)
    : (queue.addGroups groups).1.ParentRegistryClosed parents := by
  obtain ⟨_, retained, all⟩ := queue.addGroups_registration live groups
  intro ref member parent parentEq
  rcases List.mem_append.mp (queue.addGroups_registeredGroups_subset groups member) with
    old | added
  · exact retained (prior ref old parent parentEq)
  · obtain ⟨group, included, same⟩ := List.mem_map.mp added
    rcases covered group included parent
        (by rw [canonical group included, same]; exact parentEq) with prior | candidate
    · exact retained prior
    · obtain ⟨candidate, candidateMember, refEq⟩ := candidate
      exact refEq ▸ all candidate candidateMember

/-- Work integration preserves registry closure when its candidate parents are covered.
Witness: group registration supplies closure; task and stream installation leave the
resulting registry unchanged. The producer link is unrestricted.
-/
theorem State.ParentRegistryClosed.maybeIntegrateWork {queue : State} {parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    (covered : work.ParentsCovered queue.registeredGroups)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.ParentRegistryClosed parents := by
  let grouped := (queue.addGroups work.groups).1
  have taskFold (tasks : List Task) (current : State)
      : (tasks.foldl State.addTask current).registeredGroups
        = current.registeredGroups := by
    induction tasks generalizing current with
    | nil => rfl
    | cons task rest ih => exact (ih _).trans (current.addTask_registeredGroups task)
  have same : (queue.maybeIntegrateWork work parentTask).1.registeredGroups
      = grouped.registeredGroups := by
    change ((work.tasks.foldl State.addTask grouped).addStreams work.streams
      parentTask).1.registeredGroups = _
    unfold State.addStreams
    split
    · exact taskFold _ _
    · dsimp
      split <;> exact taskFold _ _
  exact (prior.addGroups live work.groups canonical covered).of_sameRegistry same

/-- A live group's named parent belongs to a closed permanent registry.
Witness: register the child, identify its canonical immediate parent, and apply closure.
-/
theorem State.ParentRegistryClosed.parent_registered {queue : State} {parents}
    (closed : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (canonical : queue.GroupParentsCanonical parents)
    {node : GroupNode} (member : node ∈ queue.groupNodes) {parent}
    (parentEq : node.group.parent = some parent)
    : parent ∈ queue.registeredGroups := by
  exact closed node.group.node.ref (live node member) parent
    ((canonical node member).symm.trans parentEq)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
