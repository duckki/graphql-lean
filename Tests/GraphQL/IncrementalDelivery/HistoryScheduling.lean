import Proofs.GraphQL.IncrementalDelivery.WorkScheduler
import Tests.GraphQL.IncrementalDelivery.WorkScheduler

/-! History-branching, shared ownership, and structural stream-item identity. -/

namespace GraphQL.IncrementalDelivery.Tests.HistoryScheduling
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkScheduler

def left : DeliveryNode := { key := 0, path := [] }
def right : DeliveryNode := { key := 1, path := [] }

def shared : Work :=
  .executionGroup [{ node := left }, { node := right }] [] (.ok ([], 0)) .empty

def matching (_ : Nat) : Occurrence := .executionGroup []

def initial : History :=
  { initialGroups := [left, right], initialStreams := [], batches := [] }

def value (owner : DeliveryNode) : WorkEvent :=
  .groupValues owner [{ path := [], data := [] }]

/-- Static navigation sees one shared task, not one task per owning defer ID. -/
theorem located_shared {address current producer owners}
    (h : Located shared address current producer owners)
    : (address = [] ∧ current = shared ∧ producer = none ∧ owners = [])
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
              WorkLocation.mk.injEq, shared, left, right]
      | succ index =>
          simp [Located, locateWork, locateWork.go, WorkLocation.child?, shared] at h

/-- All descriptor occurrences agree on a root owner with an empty response path. -/
theorem node_shared {node kind parents birth} (h : NodeAt shared node kind parents birth)
    : (node = left ∨ node = right) ∧ kind = .group ∧ parents = [] ∧ birth = none := by
  cases kind with
  | group =>
      obtain ⟨address, groups, path, result, children, enclosing, group,
        located, member, rfl, rfl⟩ := h
      rcases located_shared located with h | h <;> simp_all [shared]
      rcases member with rfl | rfl <;> simp
  | stream =>
      obtain ⟨address, items, located⟩ := h
      rcases located_shared located with h | h <;> simp_all [shared]

/-- Both initial IDs are licensed by the same still-unpublished work occurrence. -/
theorem initialized : Initializes shared [left, right] [] := by
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  have known : NodeAt shared node .group [] none := by
    simp at member
    rcases member with rfl | rfl
    · exact .group (group := { node := left }) .root (by simp)
    · exact .group (group := { node := right }) .root (by simp)
  refine ⟨
    [],
    none,
    known,
    by simp [announcedKeys, pendingKeys],
    WorkScheduler.noFailure _ _,
    Or.inr ?_,
    by simp,
    by simp
  ⟩
  intro accounted
  have owner : node.key ∈ [0, 1] := by
    rcases (node_shared known).1 with rfl | rfl <;> simp [left, right]
  have impossible := accounted (.executionGroup []) [0, 1]
    ⟨none, .object [] (.ok ([], 0)), .executionGroup .root⟩ owner
  rcases impossible with cancelled | published
  · exact WorkScheduler.noCancellation _ _ cancelled
  · simp [Published] at published

/-- Both equal-length owners are permitted; the contract does not resolve the tie. -/
theorem owner (node : DeliveryNode) (member : node ∈ [left, right])
    : Owner shared [0, 1] [] [] [0, 1] node := by
  have known : NodeAt shared node .group [] none := by
    simp at member
    rcases member with rfl | rfl
    · exact .group (group := { node := left }) .root (by simp)
    · exact .group (group := { node := right }) .root (by simp)
  have key : node.key ∈ [0, 1] := by
    rcases (node_shared known).1 with rfl | rfl <;> simp [left, right]
  refine ⟨⟨⟨.group, [], none, known⟩, key, ?_, WorkScheduler.noFailure _ _⟩, ?_⟩
  · exact ⟨by simpa [announcedKeys, pendingKeys] using key, by simp [completedKeys]⟩
  · intro other available
    obtain ⟨kind, parents, birth, otherKnown⟩ := available.1
    rcases (node_shared otherKnown).1 with rfl | rfl <;> simp [left, right]

/-- Either owner can carry the single output occurrence. -/
theorem publishes (node : DeliveryNode) (member : node ∈ [left, right])
    : EventAllowed shared [0, 1] matching [] [] (value node) := by
  refine ⟨[0, 1], none, [], [], 0, rfl, .executionGroup .root, ?_, owner node member⟩
  exact ⟨by simp [Published], WorkScheduler.noCancellation _ _, by simp, trivial⟩

/-- Empty output is an admitted prefix, with neither a selected owner nor a selected
future.
-/
theorem initialAdmitted : AdmissiblePrefix shared initial := by
  refine ⟨[], matching, [], ⟨initialized, ?_, ?_⟩, .nil⟩
  · simp [FailureWitness]
  · simp

/-- The same history admits either next owner choice, by explicit coherent occurrence
matching.
-/
theorem nextOwner (node : DeliveryNode) (member : node ∈ [left, right])
    : AdmissibleNext shared initial [value node] := by
  refine ⟨Or.inl initialAdmitted, ?_, by simp, Or.inl ?_⟩
  · intro terminal
    have count := terminal.keysCompleteExactlyOnce 0 (by simp [initial, left])
    simp [initial, completedKeys] at count
  · refine ⟨
      [value node],
      matching,
      [],
      ⟨initialized, ?_, ?_⟩,
      .cons (tail := []) (by simp) (.separate _ .nil) .nil
    ⟩
    · simp [FailureWitness]
    · intro index event selected
      cases index with
      | zero =>
          have same : event = value node := by simpa using selected.symm
          subst event
          simpa [failedBefore, initial, left, right] using publishes node member
      | succ index => simp at selected

/-- These are two different legal outputs from exactly the same observable prefix. -/
example
    : AdmissibleNext shared initial [value left]
      ∧ AdmissibleNext shared initial [value right] :=
  ⟨nextOwner left (by simp), nextOwner right (by simp)⟩

/-- Switching owner cannot publish that same structural occurrence a second time. -/
example : ¬CanPublish shared matching [value left] [] (.executionGroup []) none := by
  intro admitted
  exact admitted.1 ⟨0, value left, rfl, trivial, rfl⟩

/-- Structural inversion confirms there is only one task despite its two owners. -/
theorem task_shared {occurrence owners producer payload}
    (h : TaskAt shared occurrence owners producer payload)
    : occurrence = .executionGroup [] := by
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩ := h
      rcases located_shared located with h | h <;> simp_all [shared]
  | item address index =>
      obtain ⟨node, items, enclosing, result, children, located, entry, rfl, rfl⟩ := h
      rcases located_shared located with h | h <;> simp_all [shared]

/-- Both owners may close after the one shared publication, with neither closure ordered
first.
-/
theorem closes (node : DeliveryNode) (member : node ∈ [left, right])
    : EventAllowed shared [0, 1] matching [value left] [] (.groupSuccess node [] []) := by
  have available := (owner node member).1
  obtain ⟨kind, parents, birth, known⟩ := available.1
  obtain ⟨_, rfl, rfl, rfl⟩ := node_shared known
  refine ⟨⟨[], none, known⟩, ?_, WorkScheduler.noFailure _ _, ?_, by simp [Announcements]⟩
  · simpa [Open, announcedKeys, pendingKeys, eventPending, completedKeys, eventCompleted,
      value] using available.2.2.1
  · rintro occurrence owners ⟨producer, payload, task⟩ _
    have same := task_shared task
    subst occurrence
    exact Or.inr ⟨0, value left, rfl, trivial, rfl⟩

def publishedHistory : History := { initial with batches := [[value left]] }

/-- After publication, either completion is a legal next observable batch. -/
theorem nextClosure (node : DeliveryNode) (member : node ∈ [left, right])
    : AdmissibleNext shared publishedHistory [.groupSuccess node [] []] := by
  refine ⟨(nextOwner left (by simp)).2.2.2, ?_, by simp, Or.inl ?_⟩
  · intro terminal
    have count := terminal.keysCompleteExactlyOnce 0 (by simp [publishedHistory, initial, left])
    simp [publishedHistory, completedKeys, value, eventCompleted] at count
  · refine ⟨
      [value left, .groupSuccess node [] []],
      matching,
      [],
      ⟨initialized, ?_, ?_⟩,
      .cons (batch := [value left]) (by simp) (.separate _ .nil)
        (.cons (tail := []) (by simp) (.separate _ .nil) .nil)
    ⟩
    · simp [FailureWitness]
    · intro index event selected
      cases index with
      | zero =>
          have same : event = value left := by simpa using selected.symm
          subst event
          simpa [failedBefore, publishedHistory, initial, left, right]
            using publishes left (by simp)
      | succ index =>
          cases index with
          | zero =>
              have same : event = .groupSuccess node [] [] := by simpa using selected.symm
              subst event
              simpa [failedBefore, publishedHistory, initial, left, right]
                using closes node member
          | succ index => simp at selected

/-- No serialization of the two owner-completion notifications is built into admission. -/
example
    : AdmissibleNext shared publishedHistory [.groupSuccess left [] []]
      ∧ AdmissibleNext shared publishedHistory [.groupSuccess right [] []] :=
  ⟨nextClosure left (by simp), nextClosure right (by simp)⟩

def stream : DeliveryNode := { key := 2, path := [.field "items"] }
def items : Work := .stream stream [(.ok (.null, 0), .empty), (.ok (.null, 0), .empty)]
def itemMatching (index : Nat) : Occurrence := .item [] index
def itemValue : WorkEvent := .streamValues stream [{ item := .null }] [] []

/-- Equal values at different list positions are distinct licensed work occurrences. -/
example : TaskAt items (.item [] 0) [2] none (.item stream (.ok (.null, 0))) :=
  .item .root rfl

example : TaskAt items (.item [] 1) [2] none (.item stream (.ok (.null, 0))) :=
  .item .root rfl

example : (Occurrence.item [] 0) ≠ .item [] 1 := by decide

/-- The second item cannot publish before the first, even though their payloads are equal.
-/
example : ¬CanPublish items itemMatching [] [] (.item [] 1) none := by
  rintro ⟨_, _, _, previous⟩
  simp [Published] at previous

/-- After the first item, the second distinct occurrence is eligible for publication. -/
example : CanPublish items itemMatching [itemValue] [] (.item [] 1) none := by
  refine ⟨?_, WorkScheduler.noCancellation _ _, by simp, ?_⟩
  · rintro ⟨index, event, selected, _, equal⟩
    cases index with
    | zero => cases equal
    | succ index => simp at selected
  · exact ⟨0, itemValue, rfl, trivial, rfl⟩

/-- An actually complete history cannot acquire a further output via AdmissibleNext. -/
example {work history batch} (done : AdmissibleRun work history)
    : ¬AdmissibleNext work history batch :=
  fun next => next.2.1 done

/-- A next observation must be nonempty, independently of work and witness choices. -/
example (work : Work) (history : History) : ¬AdmissibleNext work history [] :=
  fun next => next.2.2.1 rfl

def nested : Work :=
  .executionGroup [{ node := left }] [] (.error 2)
    (.executionGroup [{ node := right }] [] (.ok ([], 0)) .empty)

/-- A nested occurrence retains its producer directly through structural navigation. -/
example
    : TaskAt nested (.executionGroup [0]) [1] (some (.executionGroup []))
        (.object [] (.ok ([], 0))) :=
  .executionGroup (.executionGroup .root)

/-- The failed producer cancels its child without a graph edge or a stored cancelled bit.
-/
example : TaskCancelled nested [.executionGroup []] (.executionGroup [0]) :=
  .producerFailed (.executionGroup (.executionGroup .root)) (by simp)

/-- Publication cannot bypass an unobserved producer even when its outcome is already
known.
-/
example
    : ¬CanPublish nested matching [] [] (.executionGroup [0])
        (some (.executionGroup [])) := by
  intro available
  have parent := available.2.2.1 (.executionGroup []) rfl
  simp [Published] at parent

def cancelledDescendant : Work :=
  .executionGroup [{ node := left }] [] (.error 2)
    (.executionGroup [{ node := right }] [] (.ok ([], 0))
      (.executionGroup [{ node := stream }] [] (.ok ([], 0)) .empty))

/-- Cancellation propagates through a cancelled producer, not only a failing producer. -/
example
    : TaskCancelled cancelledDescendant [.executionGroup []] (.executionGroup [0, 0]) :=
  .producerCancelled (.executionGroup (.executionGroup (.executionGroup .root)))
    (.producerFailed (.executionGroup (.executionGroup .root)) (by simp))

/-- A dependency can be satisfied without a success notification for an unannounced node.
-/
example {work initial matching events failed key}
    (notFailed : ¬NodeFailed work failed key)
    (unannounced : key ∉ announcedKeys initial events)
    (accounted : NodeAccounted work matching events failed key)
    : DependencySatisfied work initial matching events failed key :=
  ⟨notFailed, Or.inr (Or.inr ⟨unannounced, accounted⟩)⟩

/-- The failure refactor preserves arbitrary raw work, including repeated node metadata.
-/
example {work failed key}
    : FailureEquivalence.NodeFailed work failed key ↔ NodeFailed work failed key :=
  FailureEquivalence.nodeFailed_iff

/-- The removed wrapper carries exactly the explicit failure/cancellation alternatives. -/
example {work failed occurrence}
    : FailureEquivalence.ProducerUnavailable work failed occurrence
      ↔ occurrence ∈ failed ∨ TaskCancelled work failed occurrence :=
  FailureEquivalence.producerUnavailable_iff

namespace Lookup

def rootNode : DeliveryNode := { key := 7, path := [] }
def nestedNode : DeliveryNode := { key := 7, path := [.field "nested"] }

/-- Repeated keys have different metadata and producers in permissive raw work. -/
def repeated : Work :=
  .combine (.executionGroup [{ node := rootNode }] [] (.ok ([], 0)) .empty)
    (.executionGroup [{ node := right }] [] (.ok ([], 0))
      (.stream nestedNode [(.ok (.null, 0), .empty)]))

/-- Invalid append edges, defer edges, and stream indices have no location. -/
example
    : locateWork repeated [2] = none
      ∧ locateWork repeated [1, 1] = none
      ∧ locateWork repeated [1, 0, 1] = none :=
  ⟨rfl, rfl, rfl⟩

/-- A stream child records the absolute item producer and clears enclosing defer owners.
-/
example : locateWork repeated [1, 0, 0] = some ⟨.empty, some (.item [1, 0] 0), []⟩ := rfl

/-- Looking through combine and defer retains the actual stream-item payload and producer.
-/
example
    : TaskAt repeated (.item [1, 0] 0) [7] (some (.executionGroup [1]))
        (.item nestedNode (.ok (.null, 0))) :=
  .item (.executionGroup (.right .root)) rfl

/-- Both descriptors survive: lookup does not select one representative of a shared key.
-/
example
    : NodeAt repeated rootNode .group [] none
      ∧ NodeAt repeated nestedNode .stream [1] (some (.executionGroup [1])) := by
  constructor
  · exact .group (group := { node := rootNode }) (.left .root) (by simp)
  · exact .stream (.executionGroup (.right .root))

/-- The causal projections retain both the root and nested producer for the same key.
-/
theorem producers
    : NodeHasProducer repeated 7 none
      ∧ NodeHasProducer repeated 7 (some (.executionGroup [1])) := by
  constructor
  · exact ⟨rootNode, .group, [],
      .group (group := { node := rootNode }) (.left .root) (by simp), rfl⟩
  · exact ⟨nestedNode, .stream, [1], .stream (.executionGroup (.right .root)), rfl⟩

/-- A surviving root descriptor blocks the all-producers-unavailable rule's premise. -/
example (noRoot : ¬NodeHasProducer repeated 7 none) : False := noRoot producers.1

/-- Producer-chain reachability keeps exactly the former finite causal witnesses. -/
example {work occurrence}
    : FailureEquivalence.Reachable work occurrence ↔ Reachable work occurrence :=
  FailureEquivalence.reachable_iff

end Lookup

end GraphQL.IncrementalDelivery.Tests.HistoryScheduling
