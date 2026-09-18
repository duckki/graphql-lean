import Proofs.GraphQL.IncrementalDelivery.Correctness.SourcePositions
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StructuralEquivalence

/-! Work provenance determines the absolute paths encoded by selected owner IDs. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

/-- A located region's enclosing keys come from its nearest deferred producer; a root or
stream-item producer has no enclosing defer keys. Witness: structural navigation, which
preserves the context through append and resets it at task-producing edges.
-/
theorem located_producer_context {work address current producer owners}
    (located : Located work address current producer owners)
    : match (generalizing := false) producer with
      | none => owners = []
      | some (.deferred parent) =>
          ∃ ancestor path result,
            TaskAt work (.deferred parent) owners ancestor (.object path result)
      | some (.item _ _) => owners = [] := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => rfl
  | left _ ih | right _ ih => exact ih
  | deferred located _ => exact ⟨_, _, _, .deferred located.toCurrent⟩
  | item => rfl

/-- Structural lookup retains a generated work's coherent key-to-path assignment;
witness: address navigation, including each streamed item's child work.
-/
theorem workAt_located {paths bound work address current producer owners}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (located : Located work address current producer owners)
    : MixedOwnerPaths.WorkAt paths bound current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact coherent
  | left _ ih =>
      rw [MixedOwnerPaths.WorkAt] at ih; exact ih.1
  | right _ ih =>
      rw [MixedOwnerPaths.WorkAt] at ih; exact ih.2
  | deferred _ ih =>
      rw [MixedOwnerPaths.WorkAt] at ih; exact ih.2
  | item _ entry ih =>
      rw [MixedOwnerPaths.WorkAt] at ih
      exact ih.2 _ (List.mem_of_getElem? entry)

/-- Every node descriptor agrees with its generated key's absolute path assignment;
witness: the located defer map or stream node.
-/
theorem workAt_node {paths bound work node kind parents birth}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (known : NodeAt work node kind parents birth)
    : OwnerPaths.Assigned paths bound node := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have localWork := workAt_located coherent located.toCurrent
      rw [MixedOwnerPaths.WorkAt] at localWork
      have map := localWork.1
      apply (map _ ?_).1
      exact List.mem_flatMap.mpr ⟨_, member, by simp [OwnerPaths.fragmentNodes]⟩
  | stream located =>
      have localWork := workAt_located coherent located.toCurrent
      rw [MixedOwnerPaths.WorkAt] at localWork
      exact localWork.1

/-- Equal generated keys have equal attachment paths, even across repeated descriptors;
witness: both descriptors agree with one ghost assignment.
-/
theorem workAt_same_path
    {paths bound work left right leftKind rightKind
      leftParents rightParents leftBirth rightBirth}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (leftAt : NodeAt work left leftKind leftParents leftBirth)
    (rightAt : NodeAt work right rightKind rightParents rightBirth)
    (same : left.key = right.key)
    : left.path = right.path := by
  have hl := (workAt_node coherent leftAt).2
  have hr := (workAt_node coherent rightAt).2
  exact hl.symm.trans (same ▸ hr)

/-- A task's absolute attachment: its object path or streamed list's path. -/
def payloadPath : Payload → ResponsePath
  | .object path _ => path
  | .item node _ => node.path

/-- Every contributing owner's path is a prefix of the task's attachment path. Witness:
the task's defer map, or the identical stream-node key, and coherent metadata.
-/
theorem workAt_owner_prefix {paths bound work occurrence owners producer payload}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (task : TaskAt work occurrence owners producer payload)
    {owner kind parents birth} (known : NodeAt work owner kind parents birth)
    (contributes : owner.key ∈ owners)
    : Below owner.path (payloadPath payload) := by
  have ownerAssigned := workAt_node coherent known
  cases StructuralEquivalence.taskAt_of_current task with
  | deferred located =>
      obtain ⟨group, member, same⟩ := List.mem_map.mp contributes
      have localWork := workAt_located coherent located.toCurrent
      rw [MixedOwnerPaths.WorkAt] at localWork
      have map := localWork.1
      have hm : group.node ∈ OwnerPaths.mapNodes _ :=
        List.mem_flatMap.mpr ⟨group, member, by simp [OwnerPaths.fragmentNodes]⟩
      obtain ⟨assigned, below⟩ := map group.node hm
      have equal : owner.path = group.node.path :=
        ownerAssigned.2.symm.trans (same ▸ assigned.2)
      simpa only [payloadPath, equal] using below
  | item located _ =>
      have localWork := workAt_located coherent located.toCurrent
      rw [MixedOwnerPaths.WorkAt] at localWork
      have assigned := localWork.1
      have same := List.mem_singleton.mp contributes
      have equal : owner.path = _ :=
        ownerAssigned.2.symm.trans (same ▸ assigned.2)
      simpa only [payloadPath, equal] using below_self _

/-- An object's encoded subPath reconstructs its exact source path for every licensed
owner choice. Witness: contributing-owner prefix and list drop at the prefix length.
-/
theorem object_subPath_exact {paths bound work occurrence owners producer path result}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (task : TaskAt work occurrence owners producer (.object path result))
    {owner initial events failed}
    (selected : Owner work initial events failed owners owner)
    : owner.path ++ path.drop owner.path.length = path := by
  obtain ⟨kind, parents, birth, known⟩ := selected.1.1
  obtain ⟨suffix, equal⟩ :=
    workAt_owner_prefix coherent task known selected.1.2.1
  change path = owner.path ++ suffix at equal
  rw [equal]
  simp

end GraphQL.IncrementalDelivery.Correctness
