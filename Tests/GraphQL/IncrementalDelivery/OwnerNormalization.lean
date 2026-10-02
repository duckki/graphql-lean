import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.OwnerNormalization
import Tests.GraphQL.IncrementalDelivery.WorkQueueSemantics
import Tests.GraphQL.IncrementalDelivery.Execution

namespace GraphQL.IncrementalDelivery.Tests.OwnerNormalization
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The parent triggers publication, while the child has the shortest wire subPath. -/
def parent : DeliveryNode := { key := 0, path := [], label := some "P" }

def child : DeliveryNode := { key := 1, path := [.field "obj"], label := some "C" }
def contributors : List DeliveryNode := [parent, child]

def value : ExecutionGroupValue :=
  { path := [.field "obj"], data := [("x", .scalar "X")], deliveryGroups := contributors }

def work : Work :=
  .executionGroup [{ node := parent }, { node := child }] value.path
    (.ok (value.data, value.errors)) .empty

/-- Structural lookup exposes precisely the shared root task and its empty child. -/
theorem located_work {address current producer owners}
    (known : Located work address current producer owners)
    : (address = [] ∧ current = work ∧ producer = none ∧ owners = [])
      ∨ (address = [0]
          ∧ current = .empty
          ∧ producer = some (.executionGroup [])
          ∧ owners = [0, 1]) := by
  cases address with
  | nil => simp_all [Located, locateWork, locateWork.go, WorkLocation.mk.injEq]
  | cons index rest =>
      cases index with
      | zero =>
          cases rest <;>
            simp_all [Located, locateWork, locateWork.go, WorkLocation.child?,
              WorkLocation.mk.injEq, work, parent, child]
      | succ index =>
          simp [Located, locateWork, locateWork.go, WorkLocation.child?, work] at known

/-- The full available-owner inventory is exactly the two contributing descriptors. -/
theorem node_work {node kind parents birth} (known : NodeAt work node kind parents birth)
    : node ∈ contributors := by
  cases kind with
  | group =>
      obtain ⟨address, groups, path, result, children, enclosing, group,
        located, member, rfl, rfl⟩ := known
      rcases located_work located with h | h <;> simp_all [work, contributors]
      rcases member with rfl | rfl <;> simp
  | stream =>
      obtain ⟨address, items, located⟩ := known
      rcases located_work located with h | h <;> simp_all [work]

/-- Both contributors are open and healthy before the shared publication. -/
theorem available (node : DeliveryNode) (member : node ∈ contributors)
    : HealthyOpenOwner work [0, 1] (fun _ => .executionGroup []) [] [] [0, 1] node := by
  have known : NodeAt work node .group [] none := by
    simp [contributors] at member
    rcases member with rfl | rfl
    · exact .group (group := { node := parent }) .root (by simp)
    · exact .group (group := { node := child }) .root (by simp)
  have key : node.key ∈ [0, 1] := by
    simp [contributors] at member
    rcases member with rfl | rfl <;> simp [parent, child]
  exact ⟨
    ⟨
      ⟨.group, [], none, known⟩,
      key,
      ⟨by simpa [announcedKeys, pendingKeys] using key, by simp [completedKeys]⟩
    ⟩,
    WorkQueueSemantics.noFailure _ _
  ⟩

/-- The raw triggering group is a valid contributor but not an effective wire owner.
Witness: the open child's strictly deeper response path.
-/
example
    : HealthyOpenOwner work [0, 1] (fun _ => .executionGroup []) [] [] [0, 1] parent
      ∧ ¬PublicationOwner work [0, 1] (fun _ => .executionGroup []) [] [] [0, 1]
          parent := by
  refine ⟨available parent (by simp [contributors]), ?_⟩
  intro selected
  have bound := selected.2.2 child (available child (by simp [contributors])).1
  simp [parent, child] at bound

/-- Normalize the raw parent publication, retaining the same task, data, and errors.
Witness: the general adapter theorem derives the longest-path condition.
-/
example
    : EventAllowed work [0, 1] (fun _ => .executionGroup []) [] []
        (.groupValues (selectGroupOwner [0, 1] parent contributors) [value]) := by
  apply normalized_groupValues_allowed (owners := [0, 1]) (producer := none)
  · exact .executionGroup .root
  · exact ⟨by simp [Published], WorkQueueSemantics.noCancellation _ _, by simp, trivial⟩
  · exact available parent (by simp [contributors])
  · intro node member _
    exact (available node member).1
  · intro node active
    obtain ⟨kind, parents, birth, known⟩ := active.1
    exact ⟨node_work known, active.2.1⟩

/-- The normalized mapper reproduces the audited wire ID and both independent closures.
Initial notice order allocates C = 0 and P = 1; only C carries the shared value.
-/
def ids : IDState :=
  ((getPendingEntry (m := StateM IDState) [child, parent] [] ensureID).run {}).2

example : normalizeGroupValues [0, 1] parent [value] = [.groupValues child [value]] :=
  rfl

example
    : ((mapWorkEventBatch
          (normalizeGroupValues [0, 1] parent [value]
            ++ [
              .groupSuccess parent [] [],
              .groupSuccess child [] [],
              .workQueueTermination
            ])).run
        ids).1
      = ({
            hasNext := false
            incremental := [.object "0" value.data]
            completed := [{ id := "1" }, { id := "0" }]
          }
          : IncrementalStreamUpdateResult) :=
  rfl

/-- An unannounced or already closed deeper owner is excluded; ties keep the provisional
owner. The list of open keys, not the ever-allocated ID table, determines availability.
-/
example : selectGroupOwner [0] parent contributors = parent := rfl

example : selectGroupOwner [0, 1] child contributors = child := rfl
example : selectGroupOwner [0, 2] parent [{ key := 2, path := [] }] = parent := rfl

/-- One raw batch can need different effective owners for different values. -/
example
    : normalizeGroupValues [0, 1] parent
        [value, { value with deliveryGroups := [parent] }]
      = [
        .groupValues child [value],
        .groupValues parent [{ value with deliveryGroups := [parent] }]
      ] :=
  rfl

/-- Execution fixture matching the audited overlapping parent/child selection shape. -/
def operation : Operation :=
  {
    selectionSet :=
      [
        defer [field "user" [field "name" [] [] (some "x")] [] (some "obj")] (some "P"),
        field "user" [defer [field "name" [] [] (some "x")] (some "C")] [] (some "obj")
      ]
  }

def auditResolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ field _ _ =>
        match field with
        | "user" => some (.object "User" 1)
        | "name" => some (.scalar "X")
        | _ => none
    resolve_argumentsEquivalent := by intros; rfl
  }

def generated : Work :=
  ((executeRootSelectionSetCore schema auditResolvers [] 8 "Query" (.object "Query" 0)
      operation.selectionSet).run
    0).1.work

/-- Evaluate the execution-generated location while retaining its original combine shape.
-/
theorem generated_location
    : Located generated [0, 0, 1, 0]
        (.executionGroup [{ node := parent }, { node := child }] value.path
          (.ok (value.data, value.errors)) (.combine .empty .empty)) none [] := by
  cbv

/-- The audited owner/path/value combination is genuinely execution-generated, not only
a permissive raw-work fixture. Witness: the exact structural occurrence under combine nodes.
-/
example
    : TaskAt generated (.executionGroup [0, 0, 1, 0]) [0, 1] none
        (.object value.path (.ok (value.data, value.errors))) :=
  .executionGroup generated_location

example : NodeAt generated parent .group [] none :=
  .group (group := { node := parent }) generated_location (by simp)

example : NodeAt generated child .group [] none :=
  .group (group := { node := child }) generated_location (by simp)

/-- The raw-owner mismatch also holds on the exact execution-generated work tree.
Witness: both original descriptors are open contributors, but the child is deeper.
-/
example
    : HealthyOpenOwner generated [0, 1] (fun _ => .executionGroup [0, 0, 1, 0]) [] []
        [0, 1] parent
      ∧ ¬PublicationOwner generated [0, 1] (fun _ => .executionGroup [0, 0, 1, 0]) [] []
          [0, 1] parent := by
  have parentKnown : NodeAt generated parent .group [] none :=
    .group (group := { node := parent }) generated_location (by simp)
  have childKnown : NodeAt generated child .group [] none :=
    .group (group := { node := child }) generated_location (by simp)
  have active : HealthyOpenOwner generated [0, 1]
      (fun _ => .executionGroup [0, 0, 1, 0]) [] [] [0, 1] child :=
    ⟨⟨⟨.group, [], none, childKnown⟩, by simp [child],
      by simp [Open, announcedKeys, pendingKeys, completedKeys, child]⟩,
      WorkQueueSemantics.noFailure _ _⟩
  refine ⟨
    ⟨
      ⟨
        ⟨.group, [], none, parentKnown⟩,
        by simp [parent],
        by simp [Open, announcedKeys, pendingKeys, completedKeys, parent]
      ⟩,
      WorkQueueSemantics.noFailure _ _
    ⟩,
    ?_
  ⟩
  intro selected
  have bound := selected.2.2 child active.1
  simp [parent, child] at bound

end GraphQL.IncrementalDelivery.Tests.OwnerNormalization
