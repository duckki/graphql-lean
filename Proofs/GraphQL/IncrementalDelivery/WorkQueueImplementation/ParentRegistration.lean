import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupParents

/-! Full-chain lowering and permanent registration of primary parents. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every lowered parent appears in the same registration batch
-----------------------------------------------------------------------------------------

/-- Each primary parent named by a candidate also has a candidate in this work chunk.
The parent need not contribute to any task or remain live after integration.
-/
def Work.ParentsCovered (work : Work) : Prop :=
  ∀ group ∈ work.groups,
    ∀ parent,
      group.parent = some parent → ∃ candidate ∈ work.groups, candidate.node.key = parent

/-- A lowered ancestor chain contains every parent named by any of its entries.
Witness: induction on the nearest-first chain; the immediate parent is the final entry
of the recursively lowered tail. No generated-work assumption is required.
-/
theorem workFromSpec_groupChain_parentsCovered (nodes : List Execution.DeliveryNode)
    : ∀ group ∈ Work.fromExecution.groupChain nodes,
        ∀ parent,
          group.parent = some parent
          → ∃ candidate ∈ Work.fromExecution.groupChain nodes,
              candidate.node.key = parent := by
  induction nodes with
  | nil => simp [Work.fromExecution.groupChain]
  | cons node ancestors ih =>
      intro group member parent parentEq
      rcases List.mem_append.mp member with earlier | last
      · obtain ⟨candidate, included, same⟩ := ih group earlier parent parentEq
        exact ⟨candidate, List.mem_append_left _ included, same⟩
      · have same := List.mem_singleton.mp last
        subst group
        cases ancestors with
        | nil => cases parentEq
        | cons ancestor rest =>
            have key : ancestor.key = parent := Option.some.inj parentEq
            exact ⟨⟨ancestor, rest.head?.map Execution.DeliveryNode.key⟩,
              List.mem_append_left _ (workFromSpec_groupChain_self ancestor rest), key⟩

/-- Every lowered chunk covers its candidates' primary parents, including taskless ones.
Witness: each contributor supplies its complete chain; combination retains both lists.
-/
theorem workFromSpec_parentsCovered (work : Execution.Work) (address : Address := [])
    : (Work.fromExecution work address).ParentsCovered := by
  cases work with
  | empty => intro group member; cases member
  | stream => intro group member; cases member
  | combine left right =>
      intro group member parent parentEq
      rcases List.mem_append.mp member with inLeft | inRight
      · obtain ⟨candidate, included, same⟩ :=
          workFromSpec_parentsCovered left (address ++ [0]) group inLeft parent parentEq
        exact ⟨candidate, List.mem_append_left _ included, same⟩
      · obtain ⟨candidate, included, same⟩ :=
          workFromSpec_parentsCovered right (address ++ [1]) group inRight parent parentEq
        exact ⟨candidate, List.mem_append_right _ included, same⟩
  | executionGroup fragments path result children =>
      intro group member parent parentEq
      obtain ⟨fragment, fragmentMember, chainMember⟩ := List.mem_flatMap.mp member
      obtain ⟨candidate, included, same⟩ := workFromSpec_groupChain_parentsCovered
        (fragment.node :: fragment.ancestors) group chainMember parent parentEq
      exact ⟨candidate, List.mem_flatMap.mpr ⟨fragment, fragmentMember, included⟩, same⟩
termination_by sizeOf work

/-- Matched object success carries a child chunk with complete parent registration.
Witness: the event's exact child-work equation reduces to full-chain lowering.
-/
theorem GraphEvent.MatchesWork.childParentsCovered
    {work occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : result.work.ParentsCovered := by
  obtain ⟨_, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item => cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing, located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩ at located
      have lowering : result.work = Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      rw [lowering]
      exact workFromSpec_parentsCovered _ _

/-- A matched stream item also carries a parent-covered child chunk.
Witness: locate the supplied item and use its exact child-work lowering equation.
-/
theorem GraphEvent.MatchesWork.streamItem_parentsCovered
    {work stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : item.work.ParentsCovered := by
  obtain ⟨_, producer, known, childrenWork⟩ := matching item member
  cases occurrence : item.occurrence with
  | executionGroup => simp [streamItemWork?, occurrence] at childrenWork
  | item address index =>
      rw [occurrence] at known
      obtain ⟨node, entries, enclosing, result, children, located, entry, _, _⟩ := known
      change locateWork work address = some ⟨.stream node entries, producer, enclosing⟩ at located
      have lowering : item.work = Work.fromExecution children (address ++ [index]) := by
        simpa [streamItemWork?, occurrence, located, entry] using childrenWork.symm
      rw [lowering]
      exact workFromSpec_parentsCovered _ _

-----------------------------------------------------------------------------------------
-- The permanent registry is closed under the generated primary-parent assignment
-----------------------------------------------------------------------------------------

/-- Every registered key's assigned primary parent is permanently registered as well.
This structural property concerns the registry, not live nodes, failure health, or notices.
-/
def State.ParentRegistryClosed (queue : State) (parents : Nat → Keys) : Prop :=
  ∀ key ∈ queue.registeredGroups,
    ∀ parent, (parents key).head? = some parent → parent ∈ queue.registeredGroups

/-- Equal registries transport primary-parent closure across arbitrary metadata changes.
Witness: rewrite membership on both sides with the supplied registry equality.
-/
theorem State.ParentRegistryClosed.of_sameRegistry {before after : State} {parents}
    (prior : before.ParentRegistryClosed parents)
    (same : after.registeredGroups = before.registeredGroups)
    : after.ParentRegistryClosed parents := by
  simpa only [State.ParentRegistryClosed, same] using prior

/-- Registering a complete candidate batch preserves primary-parent registry closure.
Witness: an old key uses prior closure; a new key's canonical parent occurs in the same
batch and is registered even when its live shell is absent or registration is reused.
-/
theorem State.ParentRegistryClosed.addGroups {queue : State} {parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (groups : List Group)
    (canonical : ∀ group ∈ groups, group.parent = (parents group.node.key).head?)
    (covered
      : ∀ group ∈ groups,
          ∀ parent,
            group.parent = some parent
            → ∃ candidate ∈ groups, candidate.node.key = parent)
    : (queue.addGroups groups).1.ParentRegistryClosed parents := by
  obtain ⟨_, retained, all⟩ := queue.addGroups_registration live groups
  intro key member parent parentEq
  rcases List.mem_append.mp (queue.addGroups_registeredGroups_subset groups member) with
    old | added
  · exact retained (prior key old parent parentEq)
  · obtain ⟨group, included, same⟩ := List.mem_map.mp added
    obtain ⟨candidate, candidateMember, keyEq⟩ := covered group included parent
      (by rw [canonical group included, same]; exact parentEq)
    exact keyEq ▸ all candidate candidateMember

/-- Work integration preserves registry closure when its candidate parents are covered.
Witness: group registration supplies closure; task and stream installation leave the
resulting registry unchanged. The producer link is unrestricted.
-/
theorem State.ParentRegistryClosed.maybeIntegrateWork {queue : State} {parents}
    (prior : queue.ParentRegistryClosed parents) (live : queue.LiveGroupsRegistered)
    (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.key).head?)
    (covered : work.ParentsCovered) (parentTask : Option Occurrence := none)
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
  exact closed node.group.node.key (live node member) parent
    ((canonical node member).symm.trans parentEq)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
