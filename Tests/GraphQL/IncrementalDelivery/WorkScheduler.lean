import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureCauses
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StructuralEquivalence

/-! Structural occurrence and direct output-history regression witnesses. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkScheduler
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkScheduler

#guard_msgs (drop info) in
#check_failure Graph
#guard_msgs (drop info) in
#check_failure Progress
#guard_msgs (drop info) in
#check_failure Step
#guard_msgs (drop info) in
#check_failure ProducerUnavailable
#guard_msgs (drop info) in
#check_failure Succeeded
#guard_msgs (drop info) in
#check_failure Eligible
#guard_msgs (drop info) in
#check_failure Causality.Reachable
#guard_msgs (drop info) in
#check_failure Execution.QueryResult

def node : DeliveryNode := { key := 0, path := [] }

def single (result : Result (List (Name × ResponseValue))) : Work :=
  .deferred [{ node }] [] result .empty

def work : Work := single (.ok ([], 0))
def matching (_ : Nat) : Occurrence := .deferred []
def value : WorkEvent := .groupValues node [{ path := [], data := [] }]
def success : WorkEvent := .groupSuccess node [] []
def events : List WorkEvent := [value, success]

/-- Structural navigation has only the root task and its empty child in this fixture. -/
theorem located_single {result address current producer owners}
    (h : Located (single result) address current producer owners)
    : (address = [] ∧ current = single result ∧ producer = none ∧ owners = [])
      ∨ (address = [0]
          ∧ current = .empty
          ∧ producer = some (.deferred [])
          ∧ owners = [0]) := by
  cases address with
  | nil => simp_all [Located, locateWork, locateWork.go, WorkLocation.mk.injEq]
  | cons index rest =>
      cases index with
      | zero =>
          cases rest <;>
            simp_all [Located, locateWork, locateWork.go, WorkLocation.child?,
              WorkLocation.mk.injEq, single, node]
      | succ index =>
          simp [Located, locateWork, locateWork.go, WorkLocation.child?, single] at h

/-- A payload must name the actual structural task; equality of payloads is not its
identity.
-/
theorem task_single {result occurrence owners producer payload}
    (h : TaskAt (single result) occurrence owners producer payload)
    : occurrence = .deferred []
      ∧ owners = [0]
      ∧ producer = none
      ∧ payload = .object [] result := by
  cases occurrence with
  | deferred address =>
      obtain ⟨groups, path, value, children, enclosing, located, rfl, rfl⟩ := h
      rcases located_single located with h | h <;> simp_all [single, node]
  | item address index =>
      obtain ⟨node, items, enclosing, value, children, located, entry, rfl, rfl⟩ := h
      rcases located_single located with h | h <;> simp_all [single]

/-- Every node descriptor here refers to the one root defer node. -/
theorem node_single {result other kind parents birth}
    (h : NodeAt (single result) other kind parents birth)
    : other = node ∧ kind = .group ∧ parents = [] ∧ birth = none := by
  cases kind with
  | group =>
      obtain ⟨address, groups, path, value, children, enclosing, group,
        located, member, rfl, rfl⟩ := h
      rcases located_single located with h | h <;> simp_all [single]
  | stream =>
      obtain ⟨address, items, located⟩ := h
      rcases located_single located with h | h <;> simp_all [single]

/-- Empty failure evidence cannot justify either failed nodes or cancelled work. -/
theorem noFailure (work : Work) (key : Nat) : ¬NodeFailed work [] key :=
  fun h => h.nonempty rfl

theorem noCancellation (work : Work) (occurrence : Occurrence)
    : ¬TaskCancelled work [] occurrence :=
  fun h => h.nonempty rfl

/-- Initial notices are licensed by the root occurrence, not a compiled graph. -/
theorem initialized (result) : Initializes (single result) [node] [] := by
  refine ⟨⟨by simp, ?_, by simp⟩, by simp⟩
  intro group member
  have same : group = node := by simpa using member
  subst group
  refine ⟨[], none, (NodeAt.group (group := { node }) .root (by simp)), ?_⟩
  refine ⟨
    by simp [announcedKeys, pendingKeys],
    noFailure _ _,
    Or.inr ?_,
    by simp,
    by simp
  ⟩
  intro accounted
  have impossible := accounted (.deferred []) [0]
    ⟨none, .object [] result, .deferred .root⟩ (by simp [node])
  rcases impossible with cancelled | published
  · exact noCancellation _ _ cancelled
  · simp [Published] at published

/-- The singleton publication uses the only actual task and a fresh open owner. -/
theorem publishes : EventAllowed work [0] matching [] [] value := by
  refine ⟨[0], none, [], [], 0, rfl, .deferred .root, ?_, ?_⟩
  · exact ⟨by simp [Published], noCancellation _ _, by simp, trivial⟩
  · refine ⟨⟨⟨.group, [], none, (NodeAt.group (group := { node }) .root (by simp))⟩,
      by simp [node], by simp [Open, announcedKeys, pendingKeys, completedKeys, node],
      noFailure _ _⟩, ?_⟩
    intro other available
    obtain ⟨kind, parents, birth, known⟩ := available.1
    have same := (node_single known).1
    simp [same]

/-- Once published, the corresponding work occurrence is accounted for. -/
theorem accounted : NodeAccounted work matching [value] [] 0 := by
  rintro occurrence owners ⟨producer, payload, known⟩ _
  obtain ⟨rfl, _, _, _⟩ := task_single known
  exact Or.inr ⟨0, value, rfl, trivial, rfl⟩

/-- Success is licensed by work accounting, independently of any future termination event.
-/
theorem closes : EventAllowed work [0] matching [value] [] success := by
  refine ⟨
    ⟨[], none, (NodeAt.group (group := { node }) .root (by simp))⟩,
    ?_,
    noFailure _ _,
    accounted,
    ?_
  ⟩
  · simp [Open, announcedKeys, pendingKeys, completedKeys, value, eventPending,
      eventCompleted, node]
  · simp [Announcements]

/-- A single matching explains the entire output sequence, without internal state
transitions.
-/
theorem explained : Explains work [node] [] events matching [] := by
  refine ⟨initialized _, ?_, ?_⟩
  · simp [FailureWitness]
  · intro index event selected
    cases index with
    | zero =>
        have same : event = value := by simpa [events] using selected.symm
        subst event
        simpa [failedBefore, events, node] using publishes
    | succ index =>
        cases index with
        | zero =>
            have same : event = success := by simpa [events] using selected.symm
            subst event
            simpa [failedBefore, events, node] using closes
        | succ index => simp [events] at selected

/-- The terminal condition accounts for each occurrence and closes each announced node. -/
theorem terminal : Terminal work [0] matching events [] := by
  constructor
  · intro occurrence owners producer payload known
    obtain ⟨rfl, _, _, _⟩ := task_single known
    exact Or.inr ⟨0, value, rfl, trivial, rfl⟩
  · intro other kind parents birth known
    obtain ⟨rfl, _, _, _⟩ := node_single known
    exact Or.inl (by simp [events, completedKeys, eventCompleted, value, success, node])

/-- The public run relation admits this completed output history and its chosen batch. -/
theorem completedRun
    : AdmissibleRun work
        {
          initialGroups := [node],
          initialStreams := [],
          batches := [[value, success, .workQueueTermination]]
        } := by
  refine ⟨events, matching, [], explained, terminal, ?_⟩
  exact .cons (tail := []) (by simp) (.separate _ (.separate _ (.separate _ .nil))) .nil

/-- Stalling after initialization is admitted independently of whether it will ever
resume.
-/
theorem emptyHistory
    : AdmissiblePrefix work
        { initialGroups := [node], initialStreams := [], batches := [] } := by
  refine ⟨[], matching, [], ⟨initialized _, ?_, ?_⟩, .nil⟩
  · simp [FailureWitness]
  · simp

/-- Empty work still imposes no law on an unused source factory. -/
example (scheduler : Execution.WorkScheduler) : scheduler.Conforms .empty := by
  intro nonempty
  exact False.elim (nonempty rfl)

/-- Equal adjacent payloads remain separate occurrences unless explicitly grouped. -/
def first : WorkEvent := .groupValues node [{ path := [], data := [("a", .null)] }]

def second : WorkEvent := .groupValues node [{ path := [], data := [("b", .null)] }]

def combined : WorkEvent :=
  .groupValues node
    [{ path := [], data := [("a", .null)] }, { path := [], data := [("b", .null)] }]

example : WorkBatching [first, second] [[combined]] :=
  .cons (by simp) (.combine first (.separate second .nil) rfl) .nil

example : WorkBatching [first, second] [[first], [second]] :=
  .cons (by simp) (.separate first .nil) (.cons (by simp) (.separate second .nil) .nil)

/-- A batch must contain an observation; no empty output is manufactured from silence. -/
example : ¬WorkBatching [] [[]] := by
  intro h
  generalize original : ([] : List WorkEvent) = events at h
  cases h with
  | cons nonempty _ _ => exact nonempty (List.append_eq_nil_iff.mp original.symm).1

def failingWork : Work := single (.error 2)
def failure : WorkEvent := .groupFailure node 2

/-- A real failing occurrence supplies the causal root, independently of its notification.
-/
theorem failed : NodeFailed failingWork [.deferred []] 0 :=
  .task (.deferred .root) (by simp [node]) (by simp)

/-- That failure cancels the associated work, so it need not publish an invalid payload.
-/
theorem cancelled : TaskCancelled failingWork [.deferred []] (.deferred []) :=
  .owners (.deferred .root) (by simp [node]) (by simpa [node] using failed)

/-- The failure explanation contains one reachable failing occurrence, not an invented
error.
-/
theorem failureWitness (events : List WorkEvent)
    : FailureWitness failingWork [0] events [(0, .deferred [])] := by
  intro before cut occurrence after equal
  cases before with
  | nil =>
      have same : cut = 0 ∧ occurrence = .deferred [] ∧ after = [] := by
        simpa [Prod.mk.injEq, and_assoc] using equal.symm
      rcases same with ⟨rfl, rfl, rfl⟩
      exact ⟨
        Nat.zero_le _,
        by simp,
        ⟨
          [0],
          none,
          .object [] (.error 2),
          .deferred .root,
          rfl,
          .root ⟨[0], .object [] (.error 2), .deferred .root⟩,
          0,
          by simp,
          by simp [Open, announcedKeys, pendingKeys, completedKeys]
        ⟩,
        noCancellation _ _
      ⟩
  | cons first rest =>
      have impossible := congrArg List.length equal
      simp at impossible

/-- Failure notification uses the justified error count and the currently open node. -/
theorem reportsFailure
    : EventAllowed failingWork [0] matching [] [.deferred []] failure := by
  refine ⟨
    ⟨[], none, NodeAt.group (group := { node }) .root (by simp)⟩,
    by simp [Open, announcedKeys, pendingKeys, completedKeys, node],
    failed,
    ?_
  ⟩
  refine ⟨fun _ => 2, ?_, rfl⟩
  intro occurrence member
  have same : occurrence = .deferred [] := by simpa using member
  subst occurrence
  exact ⟨[0], none, .object [] (.error 2), .deferred .root, rfl⟩

/-- The complete failed history is admitted by structural cancellation and counted failure
evidence.
-/
theorem failedRun
    : AdmissibleRun failingWork
        {
          initialGroups := [node],
          initialStreams := [],
          batches := [[failure, .workQueueTermination]]
        } := by
  refine ⟨[failure], matching, [(0, .deferred [])], ?_, ?_, ?_⟩
  · refine ⟨initialized _, failureWitness _, ?_⟩
    intro index event selected
    cases index with
    | zero =>
        have same : event = failure := by simpa using selected.symm
        subst event
        simpa [failedBefore, node] using reportsFailure
    | succ index => simp at selected
  · constructor
    · intro occurrence owners producer payload known
      obtain ⟨rfl, _, _, _⟩ := task_single known
      exact Or.inl cancelled
    · intro other kind parents birth known
      obtain ⟨rfl, _, _, _⟩ := node_single known
      exact Or.inl (by simp [completedKeys, eventCompleted, failure])
  · exact .cons (tail := []) (by simp) (.separate _ (.separate _ .nil)) .nil

/-- A future failure cut cannot justify a failure in an earlier output prefix. -/
example : failedBefore [(1, .deferred [])] 0 = [] := rfl

/-- A successful task cannot be used as failure evidence, even if its address is genuine.
-/
example (initial : Keys) (events : List WorkEvent)
    : ¬FailureWitness work initial events [(0, .deferred [])] := by
  intro witness
  obtain ⟨owners, producer, payload, known, fails, _⟩ :=
    (witness [] 0 (.deferred []) [] rfl).2.2.1
  have result := (task_single known).2.2.2
  simp [result, Payload.failure] at fails

/-- A failure can already explain cancellation while its output notification is still
delayed.
-/
example
    : ∃ matching failures,
        Explains failingWork [node] [] [] matching failures
        ∧ NodeFailed failingWork (failedBefore failures 0) 0 := by
  exact ⟨
    matching,
    [(0, .deferred [])],
    ⟨initialized _, failureWitness [], by simp⟩,
    failed
  ⟩

end GraphQL.IncrementalDelivery.Tests.WorkScheduler
