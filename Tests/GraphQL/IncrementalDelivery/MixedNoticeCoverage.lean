import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedExistence

/-! An eligible stream can need a later carrier after shared-owner object publication. -/

namespace GraphQL.IncrementalDelivery.Tests.MixedNoticeCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open WorkScheduler

/-- Root owner, its dependent co-owner, and their produced stream use separate keys. -/
def node (key : Nat) : DeliveryNode := { key, path := [] }

/-- One shared task accounts for both owners and reveals an empty stream. -/
def work : Work :=
  .deferred [{ node := node 0 }, { node := node 1, ancestors := [node 0] }]
    [] (.ok ([], 0)) (.stream (node 2) [])

/-- Key one retains its ancestor; the stream's dependencies come from structural owners.
-/
def ancestry (key : Nat) : Keys := if key = 1 then [0] else []

/-- This fixture has one publication occurrence, independent of its chosen owner. -/
def matching (_ : Nat) : Occurrence := .deferred []

/-- The publication reports the shared selection using the announced root owner. -/
def value : WorkEvent := .groupValues (node 0) [{ path := [], data := [] }]

/-- Only the root task and its stream child can be located in this finite fixture.
Witness: direct address traversal, including rejection of nonexistent stream items.
-/
theorem located_work {address current producer owners}
    (known : Located work address current producer owners)
    : (address = [] ∧ current = work ∧ producer = none ∧ owners = [])
      ∨ (address = [0]
          ∧ current = .stream (node 2) []
          ∧ producer = some (.deferred [])
          ∧ owners = [0, 1]) := by
  cases address with
  | nil => simp_all [Located, locateWork, locateWork.go, WorkLocation.mk.injEq]
  | cons index rest =>
      cases index with
      | zero =>
          cases rest <;>
            simp_all [Located, locateWork, locateWork.go, WorkLocation.child?,
              WorkLocation.mk.injEq, work, node]
      | succ index =>
          simp [Located, locateWork, locateWork.go, WorkLocation.child?, work] at known

/-- All node metadata comes from the two shared fragments or the stream child.
Witness: the exact structural location classification.
-/
theorem node_work {other kind parents birth}
    (known : NodeAt work other kind parents birth)
    : (other = node 0 ∧ kind = .group ∧ parents = [] ∧ birth = none)
      ∨ (other = node 1 ∧ kind = .group ∧ parents = [0] ∧ birth = none)
      ∨ (other = node 2
          ∧ kind = .stream
          ∧ parents = [0, 1]
          ∧ birth = some (.deferred [])) := by
  cases kind with
  | group =>
      obtain ⟨address, groups, path, result, children, enclosing, group,
        located, member, rfl, rfl⟩ := known
      rcases located_work located with h | h <;> simp_all [work]
      rcases member with rfl | rfl <;> simp [node]
  | stream =>
      obtain ⟨address, items, located⟩ := known
      rcases located_work located with h | h <;> simp_all [work]

/-- Every task is the shared root task; the empty stream contributes no items.
Witness: structural task lookup at the only two possible work locations.
-/
theorem task_work {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = .deferred [] := by
  cases StructuralEquivalence.taskAt_of_current known with
  | deferred located =>
      rcases located_work located.toCurrent with h | h <;> simp_all [work]
  | item located selected =>
      rcases located_work located.toCurrent with h | h <;> simp_all [work]

/-- Only key zero is initially announced, and that frontier is valid.
Witness: its root descriptor has no dependencies and its shared task is still outstanding.
-/
theorem initialized : Initializes work [node 0] [] := by
  refine ⟨⟨by simp, ?_, by simp⟩, by simp⟩
  intro other member
  have same := List.mem_singleton.mp member
  subst other
  have known : NodeAt work (node 0) .group [] none :=
    .group (group := { node := node 0 }) .root (by simp)
  exact ⟨
    [],
    none,
    known,
    by simp [announcedKeys, pendingKeys],
    fun failed => failed.nonempty rfl,
    Or.inr (group_not_initially_accounted known),
    by simp,
    by simp
  ⟩

/-- The empty history is explained and the root task is ready to publish.
Witness: valid initialization and absence of prior publications or causal failures.
-/
theorem initial_ready
    : Explains work [node 0] [] [] matching []
      ∧ CanPublish work matching [] [] (.deferred []) none :=
  ⟨
    ⟨initialized, by simp [FailureWitness], by simp⟩,
    by refine ⟨by simp [Published], fun failed => failed.nonempty rfl, by simp, trivial⟩
  ⟩

/-- Initialization covers every actually eligible node in this fixture.
Witness: key one still depends on the ready root task; the stream producer is unpublished.
-/
theorem initial_covered : NoticesCovered work [0] matching [] [] := by
  intro other kind parents birth known eligible
  rcases node_work known with ⟨rfl, rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact eligible.1 (by simp [node, announcedKeys, pendingKeys])
  · exact ready_owner_dependency_unsatisfied initial_ready.1
      (show TaskAt work (.deferred []) [0, 1] none (.object [] (.ok ([], 0)))
        from .deferred .root) (by simp : 0 ∈ [0, 1]) initial_ready.2
      (by simpa [node, failedBefore] using eligible.2.2.2.2 0 (by simp))
  · have impossible := eligible.2.2.2.1 (.deferred []) rfl
    simp [Published] at impossible

/-- The actual shared object publication is admitted using the single open owner.
Witness: the event rule and equal response-path lengths for all potential owners.
-/
theorem published : Explains work [node 0] [] [value] matching [] := by
  apply initial_ready.1.append_event
  refine ⟨[0, 1], none, [], [], 0, rfl, .deferred .root, initial_ready.2, ?_⟩
  refine ⟨
    ⟨
      ⟨.group, [], none, .group (group := { node := node 0 }) .root (by simp)⟩,
      by simp [node],
      ?_,
      fun failed => failed.nonempty rfl
    ⟩,
    ?_
  ⟩
  · simp [Open, announcedKeys, pendingKeys, completedKeys, node]
  · intro other available
    obtain ⟨kind, parents, birth, known⟩ := available.1
    rcases node_work known with ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩
    all_goals simp [node]

/-- Publication silently accounts for key one, making the stream eligible immediately.
Witness: its producer has published and its unannounced co-owner is accounted for.
-/
theorem stream_eligible
    : CanAnnounce work [0] matching [value] [] (node 2) .stream
        [0, 1] (some (.deferred [])) := by
  have output : Published matching [value] (.deferred []) := ⟨0, value, rfl, trivial, rfl⟩
  refine ⟨
    by simp [node, announcedKeys, pendingKeys, value, eventPending],
    fun failed => failed.nonempty rfl,
    Or.inl rfl,
    ?_,
    Or.inr ⟨1, by simp, ?_⟩
  ⟩
  · intro parent same
    have equal := Option.some.inj same
    exact equal ▸ output
  · refine ⟨fun failed => failed.nonempty rfl, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · simp [announcedKeys, pendingKeys, value, eventPending]
    · intro occurrence owners projected _
      obtain ⟨producer, payload, known⟩ := projected
      exact Or.inr (task_work known ▸ output)

/-- Actual admission does not preserve full notice coverage across this object event.
Witness: the produced stream is eligible, but object publications carry no notices.
-/
example : ¬NoticesCovered work [0] matching [value] [] := by
  intro covered
  exact covered (node 2) .stream [0, 1] (some (.deferred []))
    (NodeAt.stream (.deferred .root)) stream_eligible

/-- Key zero remains an open, unsatisfied dependency after publication.
Witness: it is represented and announced but has no completion entry yet.
-/
theorem zero_dependency_blocked
    : ¬DependencySatisfied work [0] matching [value] [] 0 := by
  rintro ⟨_, absent | completed | ⟨fresh, _⟩⟩
  · exact absent ⟨none, node 0, .group, [],
      .group (group := { node := node 0 }) .root (by simp), rfl⟩
  · simp [completedKeys, value, eventCompleted] at completed
  · exact fresh (by simp [announcedKeys, pendingKeys, value, eventPending])

/-- The produced stream does not yet have full ancestry support, although it is eligible.
Witness: either selected co-owner requires key zero itself or its unsatisfied ancestry.
-/
theorem stream_not_supported
    : ¬SupportedNotice ancestry work [0] matching [value] []
        (node 2) .stream [0, 1] (some (.deferred [])) := by
  intro supported
  rcases supported.2 rfl with impossible | ⟨key, member, dependency, ancestors⟩
  · cases impossible
  · simp at member
    rcases member with rfl | rfl
    · exact zero_dependency_blocked dependency
    · exact zero_dependency_blocked (ancestors 0 (by simp [ancestry]))

/-- The weaker supported-notice witness survives the admitted publication.
Witness: both groups are already accounted for, while the eligible stream lacks full
ancestry support. The ordinary scheduler still permits announcing that stream earlier.
-/
theorem published_supported
    : SupportedNoticesCovered ancestry work [0] matching [value] [] := by
  have accounted (key : Nat) : NodeAccounted work matching [value] [] key := by
    intro occurrence owners projected _
    obtain ⟨producer, payload, known⟩ := projected
    exact Or.inr (task_work known ▸
      (show Published matching [value] (.deferred []) from ⟨0, value, rfl, trivial, rfl⟩))
  intro other kind parents birth known supported
  rcases node_work known with ⟨rfl, rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact supported.1.2.2.1.resolve_left (by simp) (accounted 0)
  · exact supported.1.2.2.1.resolve_left (by simp) (accounted 1)
  · exact stream_not_supported supported

/-- The same fixture still has a complete run despite losing full notice coverage.
Witness: supported mixed progress with its explicit ancestry, key roles, and paths.
The stream may wait for a later carrier under the unchanged admission rules.
-/
example : ∃ history, AdmissibleRun work history := by
  open GraphQL.IncrementalDelivery.Semantics in
  open Ancestry GeneralScheduling in
  apply mixed_completeRun_exists (ancestry := ancestry) (bound := 3)
    (roles := fun key => key == 2) (paths := fun _ => []) (pathBound := 3)
  · intro key bounded parent member
    by_cases one : key = 1
    · simp [ancestry, one] at member
      subst parent
      simp [one, ancestry, List.Subset]
    · simp [ancestry, one] at member
  · simp [work, MixedKeys.WorkAt, FragmentAt, node, ancestry]
  · simp [work, KeyRoles.WorkRoles, node]
  · simp [work, DeferContinuous, DeferUnder, node]
  · simp [work, StreamOwnersOrdered, OwnersBefore, node]
  · simp [work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simp [work, Work.size]

end GraphQL.IncrementalDelivery.Tests.MixedNoticeCoverage
