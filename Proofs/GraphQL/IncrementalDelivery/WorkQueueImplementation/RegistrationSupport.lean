import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationParentTraversal
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordInvalidation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationHistory

/-! Proof-only support for installing fresh groups below an existing live ancestor.
A fresh ref alone cannot certify installation beneath an absent parent. These witnesses
follow immutable declaration ancestry and stop at live records; they add no runtime state.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics

/-- A registration chain reaches a live record or a fresh parentless declaration. -/
inductive State.GroupRegistrationSupported (queue : State) (work : Execution.Work)
    : NodeRef → Prop
  | live {ref} (member : ref ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    : queue.GroupRegistrationSupported work ref
  | fresh {ref} (unregistered : ref ∉ queue.registeredGroups)
    (parents
      : ∀ node dependencies,
          GroupRecordAt work node dependencies
          → node.ref = ref
          → ∀ parent,
              dependencies.head? = some parent
              → queue.GroupRegistrationSupported work parent)
    : queue.GroupRegistrationSupported work ref

/-- Other queue bookkeeping may change while group records and registrations stay fixed. -/
theorem State.GroupRegistrationSupported.of_same_fields {queue next : State} {work ref}
    (supported : State.GroupRegistrationSupported queue work ref)
    (nodes : next.groupNodes = queue.groupNodes)
    (registered : next.registeredGroups = queue.registeredGroups)
    : next.GroupRegistrationSupported work ref := by
  induction supported with
  | live member => exact .live (nodes ▸ member)
  | fresh absent _ ih => exact .fresh (registered ▸ absent) ih

/-- Supported permanent registrations have a live representative. -/
theorem State.GroupRegistrationSupported.registered_live {queue work ref}
    (supported : State.GroupRegistrationSupported queue work ref)
    (registered : ref ∈ queue.registeredGroups)
    : ref ∈ queue.groupNodes.map (fun node => node.group.node.ref) := by
  cases supported with
  | live member => exact member
  | fresh absent _ => exact False.elim (absent registered)

/-- Every generated ancestry chain is supported in the empty registration state. -/
theorem ExecutedWork.empty_registrationSupported {work} (generated : ExecutedWork work)
    (ref : NodeRef)
    : ({} : State).GroupRegistrationSupported work ref := by
  induction ref using Nat.strongRecOn with
  | ind ref ih =>
      apply State.GroupRegistrationSupported.fresh (by simp)
      intro node dependencies known identity parent head
      apply ih parent
      have smaller := generated.groupRecordAncestorSmaller known (List.mem_of_head? head)
      simpa only [identity] using smaller

/-- A fresh, parent-closed generated chunk has support for all its candidates. -/
theorem State.registrationSupported_of_fresh_candidates {queue : State}
    {work : Execution.Work} (generated : ExecutedWork work) (groups : List Group)
    (fresh : ∀ group ∈ groups, group.node.ref ∉ queue.registeredGroups)
    (matching
      : ∀ group ∈ groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ groups,
          ∀ parent,
            group.parent = some parent
            → ∃ candidate ∈ groups, candidate.node.ref = parent)
    : ∀ group ∈ groups, queue.GroupRegistrationSupported work group.node.ref := by
  have descend (ref : NodeRef) : ∀ group ∈ groups, group.node.ref = ref
      → queue.GroupRegistrationSupported work ref := by
    induction ref using Nat.strongRecOn with
    | ind ref ih =>
        intro group member identity
        apply State.GroupRegistrationSupported.fresh (identity ▸ fresh group member)
        intro node dependencies known sameRef parent head
        obtain ⟨ancestors, groupKnown, canonical⟩ := matching group member
        obtain ⟨parents, assignment⟩ := generated.groupRecordsCanonical
        have same : dependencies = ancestors := by
          rw [assignment node dependencies known, assignment group.node ancestors groupKnown,
            sameRef, identity]
        have parentEq : group.parent = some parent := canonical.trans (same ▸ head)
        obtain ⟨candidate, parentMember, parentRef⟩ := closed group member parent parentEq
        exact ih parent
          (by
            have smaller :=
              generated.groupRecordAncestorSmaller known (List.mem_of_head? head)
            simpa only [sameRef] using smaller)
          candidate parentMember parentRef
  exact fun group member => descend group.node.ref group member rfl

/-- A healthy chain below a live contributing ancestor has registration support.
The retirement premise is proof evidence derived from replay, not a source law.
-/
theorem State.groupRegistrationSupported_of_live_ancestor {queue : State}
    {work failed owner} (generated : ExecutedWork work)
    (ownerLive : owner ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    (protection
      : ∀ node dependencies,
          GroupRecordAt work node dependencies
          → ¬GroupRecordInvalidated work failed node.ref
          → owner ∈ dependencies
          → queue.RetiredGroup node.ref
          → False)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    (healthy : ¬GroupRecordInvalidated work failed node.ref)
    (ancestor : owner = node.ref ∨ owner ∈ dependencies)
    : queue.GroupRegistrationSupported work node.ref := by
  have descend (ref : NodeRef) : ∀ node dependencies, node.ref = ref
      → GroupRecordAt work node dependencies
      → ¬GroupRecordInvalidated work failed ref
      → (owner = ref ∨ owner ∈ dependencies)
      → queue.GroupRegistrationSupported work ref := by
    induction ref using Nat.strongRecOn with
    | ind ref ih =>
        intro node dependencies identity known healthy ancestor
        rcases ancestor with same | ancestor
        · exact .live (same ▸ ownerLive)
        by_cases registered : ref ∈ queue.registeredGroups
        · cases found : queue.groupNode? ref with
          | some live => exact .live (List.mem_map.mpr
              ⟨live, List.mem_of_find?_eq_some found, State.groupNode?_ref found⟩)
          | none =>
              apply False.elim
              apply protection node dependencies known (identity ▸ healthy) ancestor
              refine ⟨identity ▸ registered, ?_⟩
              intro member
              obtain ⟨live, included, same⟩ := List.mem_map.mp member
              exact List.find?_eq_none.mp found live included (beq_iff_eq.mpr (same.trans identity))
        · apply State.GroupRegistrationSupported.fresh registered
          intro other rest otherKnown sameRef parent head
          obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
          have sameDependencies : rest = dependencies := by
            rw [canonical other rest otherKnown, canonical node dependencies known,
              sameRef, identity]
          subst rest
          cases dependencies with
          | nil => cases head
          | cons first tail =>
              have equal : first = parent := Option.some.inj head
              subst first
              obtain ⟨parentNode, parentRef, parentKnown⟩ := otherKnown.parent
              apply ih parent
                (by
                  have smaller :=
                    generated.groupRecordAncestorSmaller (ancestor := parent) otherKnown
                      (by simp)
                  simpa only [sameRef] using smaller)
                parentNode tail parentRef parentKnown
              · intro invalid
                exact healthy (sameRef ▸ GroupRecordInvalidated.ancestor otherKnown (by simp) invalid)
              · exact List.mem_cons.mp ancestor
  exact descend node.ref node dependencies rfl known healthy ancestor

/-- Installation preserves supported ancestry when its parent is already registered. -/
theorem State.GroupRegistrationSupported.addGroup {queue work ref}
    (supported : State.GroupRegistrationSupported queue work ref) (group : Group)
    (matching
      : ∃ dependencies,
          GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head?)
    (parentRegistered
      : ∀ parent, group.parent = some parent → parent ∈ queue.registeredGroups)
    : (queue.addGroup group).GroupRegistrationSupported work ref := by
  induction supported with
  | live member => exact .live (queue.addGroup_refs_subset group member)
  | @fresh ref unregistered parents ih =>
      by_cases same : ref = group.node.ref
      · subst ref
        have makeLive : group.node.ref ∈ (queue.addGroup group).groupNodes.map
            (fun node => node.group.node.ref) := by
          cases found : queue.groupNode? group.node.ref with
          | some node =>
              simp only [State.addGroup, found, Option.isSome_some, Bool.or_true, ite_true]
              exact List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, State.groupNode?_ref found⟩
          | none =>
              cases parentEq : group.parent with
              | none => simp [State.addGroup, unregistered, found, parentEq]
              | some parent =>
                  obtain ⟨dependencies, known, canonical⟩ := matching
                  have parentSupported := parents group.node dependencies known rfl parent
                    (canonical.symm.trans parentEq)
                  have live := parentSupported.registered_live (parentRegistered parent parentEq)
                  cases parentFound : queue.groupNode? parent with
                  | none =>
                      obtain ⟨node, member, identity⟩ := List.mem_map.mp live
                      exact False.elim (List.find?_eq_none.mp parentFound node member
                        (beq_iff_eq.mpr identity))
                  | some node =>
                      simp only [State.addGroup, show queue.registeredGroups.contains group.node.ref = false
                          by simpa using unregistered, found, Option.isSome_none, Bool.or_self,
                        Bool.false_eq_true, ite_false, parentEq, parentFound]
                      rw [State.putGroupNode_refs]
                      simp
        exact .live makeLive
      · apply State.GroupRegistrationSupported.fresh
        · intro registered
          rcases List.mem_append.mp (queue.addGroup_registeredGroups_subset group registered) with
            old | new
          · exact unregistered old
          · exact same (List.mem_singleton.mp new)
        · exact ih

/-- Parent-first registration preserves an ancestry support witness.
Candidate parents are visited first; inherited parents use the permanent input registry.
-/
theorem State.GroupRegistrationSupported.addGroups {queue work ref}
    (supported : State.GroupRegistrationSupported queue work ref)
    (generated : ExecutedWork work) (coverage : queue.LiveGroupsRegistered)
    (groups : List Group)
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
    : (queue.addGroups groups).1.GroupRegistrationSupported work ref := by
  let property (current : State) := current.GroupRegistrationSupported work ref
    ∧ queue.registeredGroups ⊆ current.registeredGroups
  have ordered : ∀ group ∈ groups, ∀ parent, group.parent = some parent → parent < group.node.ref := by
    intro group member parent parentEq
    obtain ⟨dependencies, known, canonical⟩ := matching group member
    exact generated.groupRecordAncestorSmaller known
      (List.mem_of_head? (canonical.symm.trans parentEq))
  exact (State.addGroups_preserves_parentRegistered property groups ordered
    (fun current group member _ parents valid =>
      ⟨valid.1.addGroup group (matching group member) (fun parent parentEq =>
        (List.mem_append.mp (closed group member parent parentEq)).elim
          (fun old => valid.2 old) (parents parent parentEq)),
        valid.2.trans (current.addGroup_registeredGroups_subset_old group)⟩)
    queue coverage ⟨supported, List.Subset.refl _⟩).1

/-- A supported candidate is live after its parent-first registration batch. -/
theorem State.addGroups_supported_live {queue work ref}
    (supported : State.GroupRegistrationSupported queue work ref)
    (generated : ExecutedWork work) (coverage : queue.LiveGroupsRegistered)
    (groups : List Group)
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
    (candidate : ref ∈ groups.map (fun group => group.node.ref))
    : ref
      ∈ (queue.addGroups groups).1.groupNodes.map (fun node => node.group.node.ref) := by
  apply (supported.addGroups generated coverage groups matching closed).registered_live
  obtain ⟨group, member, identity⟩ := List.mem_map.mp candidate
  exact identity ▸ (queue.addGroups_registration coverage groups).2.2 group member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
