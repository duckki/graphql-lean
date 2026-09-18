import GraphQL.IncrementalDelivery.Execution

/-! Output-history semantics for the finite pure-outcome model.
Admission relates Work to observations, not to an internal queue, graph, or progress
machine. Structural occurrences distinguish equal payloads and shared work. Existential
publication matching and failure cuts explain a history; neither selects its future.

Read EventAllowed for the event rules. Its helpers answer three questions: what work
exists, what has been observed, and what failures justify cancellation. They describe
work and its observations, not runtime workers or an internal scheduler state.
-/

namespace GraphQL.IncrementalDelivery
open GraphQL.IncrementalDelivery.Execution

namespace WorkScheduler

-----------------------------------------------------------------------------------------
-- What work exists?
-----------------------------------------------------------------------------------------

/-- A structural route through Work; unrelated to a response path or delivery-node key. -/
abbrev Address := List Nat

/-- Ordered delivery-node keys; distinct from task occurrences and allocated wire IDs. -/
abbrev Keys := List Nat

inductive NodeKind where
  | group
  | stream
deriving Repr, BEq, DecidableEq

/-- Addresses are structural positions in Work, not allocated scheduler task IDs. -/
inductive Occurrence where
  | deferred (address : Address)
  | item (address : Address) (index : Nat)
deriving Repr, BEq, DecidableEq

inductive Payload where
  | object (path : ResponsePath) (result : Result (List (Name × ResponseValue)))
  | item (node : DeliveryNode) (result : Result ResponseValue)
deriving Repr

def Payload.failure : Payload → Option Nat
  | .object _ (.error errors) | .item _ (.error errors) => some errors
  | _ => none

/-- A view of existing work and its context, not a task graph or scheduler state. -/
structure WorkLocation where
  current : Work
  producer : Option Occurrence
  owners : Keys

/-- Descend one structural edge, retaining the absolute address of any producer. -/
def WorkLocation.child? (location : WorkLocation) (address : Address) (index : Nat)
    : Option WorkLocation :=
  match location.current, index with
  | .append left _, 0 => some { location with current := left }
  | .append _ right, 1 => some { location with current := right }
  | .deferred groups _ _ children, 0 =>
      some ⟨children, some (.deferred address), groups.map (fun group => group.node.key)⟩
  | .stream _ items, index =>
      items[index]?.map (fun entry => ⟨entry.2, some (.item address index), []⟩)
  | _, _ => none

/-- Follow an address in work; invalid edges have no location. No keys are deduplicated.
-/
def locateWork (work : Work) (address : Address) : Option WorkLocation :=
  go [] ⟨work, none, []⟩ address
where
  /-- Consume the remaining route while retaining its absolute address prefix. -/
  go (route : Address) (location : WorkLocation) : Address → Option WorkLocation
    | [] => some location
    | index :: rest => do
        let child ← location.child? route index
        go (route ++ [index]) child rest

/-- The address identifies this subwork, generating task, and enclosing defer keys. -/
def Located (root : Work) (address : Address) (current : Work)
    (producer : Option Occurrence) (owners : Keys)
    : Prop :=
  locateWork root address = some ⟨current, producer, owners⟩

/-- The structural occurrence identifies a task with these owners, producer, and payload.
-/
def TaskAt (work : Work) (occurrence : Occurrence) (owners : Keys)
    (producer : Option Occurrence) (payload : Payload)
    : Prop :=
  match occurrence with
  | .deferred address =>
      ∃ groups path result children enclosing,
        Located work address (.deferred groups path result children) producer enclosing
        ∧ owners = groups.map (fun group => group.node.key)
        ∧ payload = .object path result
  | .item address index =>
      ∃ node items enclosing result children,
        Located work address (.stream node items) producer enclosing
        ∧ items[index]? = some (result, children)
        ∧ owners = [node.key]
        ∧ payload = .item node result

/-- Some location contains this node descriptor. Repeated keys retain every descriptor.
-/
def NodeAt (work : Work) (node : DeliveryNode) (kind : NodeKind) (parents : Keys)
    (birth : Option Occurrence)
    : Prop :=
  match kind with
  | .group =>
      ∃ address groups path result children enclosing group,
        Located work address (.deferred groups path result children) birth enclosing
        ∧ group ∈ groups
        ∧ node = group.node
        ∧ parents = group.ancestors.map DeliveryNode.key
  | .stream => ∃ address items, Located work address (.stream node items) birth parents

/-- The task has exactly this list of contributing owner keys. -/
def TaskHasOwners (work : Work) (occurrence : Occurrence) (owners : Keys) : Prop :=
  ∃ producer payload, TaskAt work occurrence owners producer payload

/-- The task has this generating occurrence, or is a root task when producer is none. -/
def TaskHasProducer (work : Work) (occurrence : Occurrence) (producer : Option Occurrence)
    : Prop :=
  ∃ owners payload, TaskAt work occurrence owners producer payload

/-- The task's fixed outcome is successful; this does not assert publication. -/
def TaskSucceeds (work : Work) (occurrence : Occurrence) : Prop :=
  ∃ owners producer payload,
    TaskAt work occurrence owners producer payload ∧ payload.failure = none

/-- Some descriptor with this key and kind has these dependency keys. -/
def NodeHasParents (work : Work) (key : Nat) (kind : NodeKind) (parents : Keys) : Prop :=
  ∃ node birth, NodeAt work node kind parents birth ∧ node.key = key

/-- Some descriptor with this key has this producer; repeated descriptors are retained. -/
def NodeHasProducer (work : Work) (key : Nat) (producer : Option Occurrence) : Prop :=
  ∃ node kind parents, NodeAt work node kind parents producer ∧ node.key = key

/-- (Reachable work occurrence) derives a successful producer chain for the occurrence. -/
inductive Reachable (work : Work) : Occurrence → Prop where
  | root {occurrence} (known : TaskHasProducer work occurrence none)
    : Reachable work occurrence
  | child {occurrence parent} (known : TaskHasProducer work occurrence (some parent))
    (success : TaskSucceeds work parent) (reachable : Reachable work parent)
    : Reachable work occurrence

-----------------------------------------------------------------------------------------
-- Which failures justify cancellation?
-----------------------------------------------------------------------------------------

/-- Ordered (output-prefix length, failing occurrence) evidence, not host timestamps. -/
abbrev FailureCuts := List (Nat × Occurrence)

/-! A failure may precede its notification. Failure cuts record that hidden evidence;
the causal rules below derive its consequences without an internal scheduler state.
Cut i means after initialization and before output i, not host time. Only real failing
work with successful producers and an open contributing owner may enter the witness.
Cancellation uses earlier failures, never a self-justifying cycle.
-/

namespace Causality

mutual
  /-- (NodeFailed work failed key) is the least closure of task failures and dependencies.
  -/
  inductive NodeFailed (work : Work) (failed : List Occurrence) : Nat → Prop where
    | task {occurrence owners key} (known : TaskHasOwners work occurrence owners)
      (owner : key ∈ owners) (finished : occurrence ∈ failed)
      : NodeFailed work failed key
    | groupParent {key parents parent} (known : NodeHasParents work key .group parents)
      (member : parent ∈ parents) (failure : NodeFailed work failed parent)
      : NodeFailed work failed key
    | streamParents {key parents} (known : NodeHasParents work key .stream parents)
      (nonempty : parents ≠ [])
      (failures : ∀ parent ∈ parents, NodeFailed work failed parent)
      : NodeFailed work failed key
    /-- Every descriptor's producer is unavailable; any root descriptor blocks this rule.
    -/
    | producers {key} (known : ∃ birth, NodeHasProducer work key birth)
      (noRoot : ¬NodeHasProducer work key none)
      (cancelled
        : ∀ parent,
            NodeHasProducer work key (some parent)
            → parent ∉ failed
            → TaskCancelled work failed parent)
      : NodeFailed work failed key

  /-- (TaskCancelled work failed occurrence) derives cancellation, never a circular cause.
  -/
  inductive TaskCancelled (work : Work) (failed : List Occurrence)
      : Occurrence → Prop where
    | owners {occurrence owners} (known : TaskHasOwners work occurrence owners)
      (nonempty : owners ≠ []) (failures : ∀ key ∈ owners, NodeFailed work failed key)
      : TaskCancelled work failed occurrence
    | producerFailed {occurrence parent}
      (known : TaskHasProducer work occurrence (some parent)) (failure : parent ∈ failed)
      : TaskCancelled work failed occurrence
    | producerCancelled {occurrence parent}
      (known : TaskHasProducer work occurrence (some parent))
      (cancelled : TaskCancelled work failed parent)
      : TaskCancelled work failed occurrence
end

end Causality

/-- The supplied failed occurrences causally imply failure of this node key. -/
def NodeFailed (work : Work) (failed : List Occurrence) (key : Nat) : Prop :=
  Causality.NodeFailed work failed key

/-- The supplied failures causally cancel this task; cycles alone do not suffice.
-/
def TaskCancelled (work : Work) (failed : List Occurrence) (occurrence : Occurrence)
    : Prop :=
  Causality.TaskCancelled work failed occurrence

def failedBefore (failures : FailureCuts) (cut : Nat) : List Occurrence :=
  (failures.filter (fun entry => entry.1 ≤ cut)).map Prod.snd

-----------------------------------------------------------------------------------------
-- What has been observed?
-----------------------------------------------------------------------------------------

/-- Maps zero-based unbatched work-event indices to producing work occurrences.
Indices precede grouping or batching; only value-publication indices are used.
-/
abbrev PublicationMatching := Nat → Occurrence

def eventPending : WorkEvent → Keys
  | .groupSuccess _ groups streams | .streamValues _ _ groups streams =>
      (groups ++ streams).map DeliveryNode.key
  | _ => []

def eventCompleted : WorkEvent → Keys
  | .groupSuccess node ..
  | .groupFailure node _
  | .streamSuccess node
  | .streamFailure node _ => [node.key]
  | _ => []

def pendingKeys (events : List WorkEvent) : Keys := events.flatMap eventPending
def completedKeys (events : List WorkEvent) : Keys := events.flatMap eventCompleted

/-- (IsValue event) classifies the supplied work event as a value publication rather than
control.
-/
def IsValue : WorkEvent → Prop
  | .groupValues .. | .streamValues .. => True
  | _ => False

/-- The occurrence has a value publication in the observed prefix, identified by the
matching shared across the entire history.
-/
def Published (matching : PublicationMatching) (events : List WorkEvent)
    (occurrence : Occurrence)
    : Prop :=
  ∃ index event, events[index]? = some event ∧ IsValue event ∧ matching index = occurrence

def announcedKeys (initial : Keys) (events : List WorkEvent) : Keys :=
  initial ++ pendingKeys events

/-- The node key has been announced initially or in the output prefix, but not yet closed.
-/
def Open (initial : Keys) (events : List WorkEvent) (key : Nat) : Prop :=
  key ∈ announcedKeys initial events ∧ key ∉ completedKeys events

/-- Ordered failure cuts for reachable, uncancelled failing tasks. Each failure has an
open contributing owner in the observed prefix at its cut; notification may follow later.
The output length bounds every cut, including the final cut. Unannounced failures cannot
silently cancel work and satisfy termination without a failure completion. Failure
occurrences are necessarily unique: an earlier copy would already cancel the task.
-/
def FailureWitness (work : Work) (initial : Keys) (events : List WorkEvent)
    (failures : FailureCuts)
    : Prop :=
  ∀ before cut occurrence after,
    failures = before ++ (cut, occurrence) :: after
    → cut ≤ events.length
      ∧ (∀ earlier ∈ before, earlier.1 ≤ cut)
      ∧ (∃ owners producer payload,
          TaskAt work occurrence owners producer payload
          ∧ payload.failure.isSome = true
          ∧ Reachable work occurrence
          ∧ ∃ key ∈ owners, Open initial (events.take cut) key)
      ∧ ¬TaskCancelled work (before.map Prod.snd) occurrence

-----------------------------------------------------------------------------------------
-- Which events are permitted?
-----------------------------------------------------------------------------------------

/-! EventAllowed combines publication readiness, contributing-owner choice, and fresh
announcements. Successful closure additionally accounts for every contributing task.
-/

/-- The task occurrence has been published or causally cancelled by known failures. -/
def Accounted (work : Work) (matching : PublicationMatching) (events : List WorkEvent)
    (failed : List Occurrence) (occurrence : Occurrence)
    : Prop :=
  TaskCancelled work failed occurrence ∨ Published matching events occurrence

/-- Every task contributing to the node key has been published or cancelled. -/
def NodeAccounted (work : Work) (matching : PublicationMatching) (events : List WorkEvent)
    (failed : List Occurrence) (key : Nat)
    : Prop :=
  ∀ occurrence owners,
    TaskHasOwners work occurrence owners
    → key ∈ owners
    → Accounted work matching events failed occurrence

/-- The node key has not failed and is absent, completed, or unannounced with all
contributing tasks accounted for.
-/
def DependencySatisfied (work : Work) (initial : Keys) (matching : PublicationMatching)
    (events : List WorkEvent) (failed : List Occurrence) (key : Nat)
    : Prop :=
  ¬NodeFailed work failed key
  ∧ ((¬∃ birth, NodeHasProducer work key birth)
      ∨ key ∈ completedKeys events
      ∨ key ∉ announcedKeys initial events
        ∧ NodeAccounted work matching events failed key)

/-- The node may be announced after its producer publishes and its dependencies are
satisfied. Groups require all parent keys; streams require one, unless there are none.
-/
def CanAnnounce (work : Work) (initial : Keys) (matching : PublicationMatching)
    (events : List WorkEvent) (failed : List Occurrence) (node : DeliveryNode)
    (kind : NodeKind) (parents : Keys) (birth : Option Occurrence)
    : Prop :=
  node.key ∉ announcedKeys initial events
  ∧ ¬NodeFailed work failed node.key
  ∧ (kind = .stream ∨ ¬NodeAccounted work matching events failed node.key)
  ∧ (∀ producer, birth = some producer → Published matching events producer)
  ∧ match kind with
    | .group =>
        ∀ key ∈ parents, DependencySatisfied work initial matching events failed key
    | .stream =>
        parents = []
        ∨ ∃ key ∈ parents, DependencySatisfied work initial matching events failed key

/-- Fresh, distinct group and stream notices whose nodes are eligible after the observed
prefix.
-/
def Announcements (work : Work) (initial : Keys) (matching : PublicationMatching)
    (events : List WorkEvent) (failed : List Occurrence)
    (groups streams : List DeliveryNode)
    : Prop :=
  ((groups ++ streams).map DeliveryNode.key).Nodup
  ∧ (∀ group ∈ groups,
      ∃ parents birth,
        NodeAt work group .group parents birth
        ∧ CanAnnounce work initial matching events failed group .group parents birth)
  ∧ (∀ stream ∈ streams,
      ∃ parents birth,
        NodeAt work stream .stream parents birth
        ∧ CanAnnounce work initial matching events failed stream .stream parents birth)

/-- A nonempty initial frontier of eligible group and stream notices. -/
def Initializes (work : Work) (groups streams : List DeliveryNode) : Prop :=
  Announcements work [] (fun _ => .deferred []) [] [] groups streams
  ∧ groups ++ streams ≠ []

/-- The candidate is a known contributing owner that is announced, open, and not failed.
-/
def AvailableOwner (work : Work) (initial : Keys) (events : List WorkEvent)
    (failed : List Occurrence) (owners : Keys) (node : DeliveryNode)
    : Prop :=
  (∃ kind parents birth, NodeAt work node kind parents birth)
  ∧ node.key ∈ owners
  ∧ Open initial events node.key
  ∧ ¬NodeFailed work failed node.key

/-- An available contributing owner with a longest response path; ties are allowed. -/
def Owner (work : Work) (initial : Keys) (events : List WorkEvent)
    (failed : List Occurrence) (owners : Keys) (node : DeliveryNode)
    : Prop :=
  AvailableOwner work initial events failed owners node
  ∧ ∀ other,
      AvailableOwner work initial events failed owners other
      → other.path.length ≤ node.path.length

/-- The occurrence is unpublished and uncancelled, with its producer already published. A
noninitial stream item also requires publication of the preceding item.
-/
def CanPublish (work : Work) (matching : PublicationMatching) (events : List WorkEvent)
    (failed : List Occurrence) (occurrence : Occurrence) (producer : Option Occurrence)
    : Prop :=
  ¬Published matching events occurrence
  ∧ ¬TaskCancelled work failed occurrence
  ∧ (∀ parent, producer = some parent → Published matching events parent)
  ∧ match occurrence with
    | .item address (index + 1) => Published matching events (.item address index)
    | _ => True

/-- The claimed error count sums failures of tasks contributing to the node key. -/
def NodeErrors (work : Work) (failed : List Occurrence) (key errors : Nat) : Prop :=
  ∃ contribution : Occurrence → Nat,
    (∀ occurrence ∈ failed,
      ∃ owners producer payload,
        TaskAt work occurrence owners producer payload
        ∧ contribution occurrence = if key ∈ owners then payload.failure.getD 0 else 0)
    ∧ errors = (failed.map contribution).sum

/-- The next atomic event has valid provenance, dependencies, ownership, and notices
relative to the observed prefix and known failures. New notices follow the carrier.
-/
def EventAllowed (work : Work) (initial : Keys) (matching : PublicationMatching)
    (before : List WorkEvent) (failed : List Occurrence) (event : WorkEvent)
    : Prop :=
  match event with
  | .groupValues node values =>
      ∃ owners producer path data errors,
        values = [{ path, data, errors }]
        ∧ TaskAt work (matching before.length) owners producer
            (.object path (.ok (data, errors)))
        ∧ CanPublish work matching before failed (matching before.length) producer
        ∧ Owner work initial before failed owners node
  | .streamValues node values groups streams =>
      ∃ owners producer item errors,
        values = [{ item, errors }]
        ∧ TaskAt work (matching before.length) owners producer
            (.item node (.ok (item, errors)))
        ∧ CanPublish work matching before failed (matching before.length) producer
        ∧ Owner work initial before failed owners node
        ∧ Announcements work initial matching
            (before ++ [.streamValues node values [] []]) failed groups streams
  | .groupSuccess node groups streams =>
      (∃ parents birth, NodeAt work node .group parents birth)
      ∧ Open initial before node.key
      ∧ ¬NodeFailed work failed node.key
      ∧ NodeAccounted work matching before failed node.key
      ∧ Announcements work initial matching
          (before ++ [.groupSuccess node [] []]) failed groups streams
  | .streamSuccess node =>
      (∃ parents birth, NodeAt work node .stream parents birth)
      ∧ Open initial before node.key
      ∧ ¬NodeFailed work failed node.key
      ∧ NodeAccounted work matching before failed node.key
  | .groupFailure node errors =>
      (∃ parents birth, NodeAt work node .group parents birth)
      ∧ Open initial before node.key
      ∧ NodeFailed work failed node.key
      ∧ NodeErrors work failed node.key errors
  | .streamFailure node errors =>
      (∃ parents birth, NodeAt work node .stream parents birth)
      ∧ Open initial before node.key
      ∧ NodeFailed work failed node.key
      ∧ NodeErrors work failed node.key errors
  | .workQueueTermination => False

-----------------------------------------------------------------------------------------
-- Admitted histories and batching
-----------------------------------------------------------------------------------------

/-- Initial notices and atomic outputs follow the work rules under one publication
matching and bounded failure cuts. No wire correctness or eventual progress is assumed.
-/
def Explains (work : Work) (groups streams : List DeliveryNode) (events : List WorkEvent)
    (matching : PublicationMatching) (failures : FailureCuts)
    : Prop :=
  Initializes work groups streams
  ∧ FailureWitness work ((groups ++ streams).map DeliveryNode.key) events failures
  ∧ ∀ index event,
      events[index]? = some event
      → EventAllowed work ((groups ++ streams).map DeliveryNode.key) matching
          (events.take index) (failedBefore failures index) event

/-- All tasks are accounted for, and every node is closed or unannounced and failed or
accounted for.
-/
def Terminal (work : Work) (initial : Keys) (matching : PublicationMatching)
    (events : List WorkEvent) (failed : List Occurrence)
    : Prop :=
  (∀ occurrence owners producer payload,
    TaskAt work occurrence owners producer payload
    → Accounted work matching events failed occurrence)
  ∧ ∀ node kind parents birth,
      NodeAt work node kind parents birth
      → node.key ∈ completedKeys events
        ∨ node.key ∉ announcedKeys initial events
          ∧ (NodeFailed work failed node.key
              ∨ NodeAccounted work matching events failed node.key)

/-- Adjacent compatible value events may be represented by a single spec event with
multiple values. This is independent of work-event and response-event batching.
-/
def combineValues : WorkEvent → WorkEvent → Option WorkEvent
  | .groupValues group left, .groupValues other right =>
      if group.key == other.key then some (.groupValues group (left ++ right)) else none
  | .streamValues stream left groups streams,
    .streamValues other right moreGroups moreStreams =>
      if stream.key == other.key then
        some
          (.streamValues stream (left ++ right) (groups ++ moreGroups)
            (streams ++ moreStreams))
      else
        none
  | _, _ => none

/-- (ValueGrouping events grouped) relates input atoms events to grouped outputs obtained
by optional adjacent compatible-value coalescing, preserving value order and contents.
-/
inductive ValueGrouping : List WorkEvent → List WorkEvent → Prop where
  | nil : ValueGrouping [] []
  | separate (head) {tail grouped} (rest : ValueGrouping tail grouped)
    : ValueGrouping (head :: tail) (head :: grouped)
  | combine (head) {tail first rest merged}
    (grouped : ValueGrouping tail (first :: rest))
    (compatible : combineValues head first = some merged)
    : ValueGrouping (head :: tail) (merged :: rest)

/-- (WorkBatching events batches) partitions atomic outputs events into nonempty batches,
with optional value coalescing inside each output batch in batches.
-/
inductive WorkBatching : List WorkEvent → List (List WorkEvent) → Prop where
  | nil : WorkBatching [] []
  | cons {batch tail grouped rest}
    (nonempty : batch ≠ [])
    (values : ValueGrouping batch grouped)
    (subsequent : WorkBatching tail rest)
    : WorkBatching (batch ++ tail) (grouped :: rest)

structure History where
  initialGroups : List DeliveryNode
  initialStreams : List DeliveryNode
  batches : List (List WorkEvent)
deriving Repr

/-- Admitted initial notices and batches, allowing stalled or interrupted output without a
completion requirement.
-/
def AdmissiblePrefix (work : Work) (history : History) : Prop :=
  ∃ events matching failures,
    Explains work history.initialGroups history.initialStreams events matching failures
    ∧ WorkBatching events history.batches

/-- An admitted history accounting for all work before exactly one final termination
marker.
-/
def AdmissibleRun (work : Work) (history : History) : Prop :=
  ∃ events matching failures,
    Explains work history.initialGroups history.initialStreams events matching failures
    ∧ Terminal work
        ((history.initialGroups ++ history.initialStreams).map DeliveryNode.key) matching
        events (failedBefore failures events.length)
    ∧ WorkBatching (events ++ [.workQueueTermination]) history.batches

/-- An admitted prefix or terminal run. -/
def ValidHistory (work : Work) (history : History) : Prop :=
  AdmissiblePrefix work history ∨ AdmissibleRun work history

/-- A nonempty batch may extend the valid, nonterminal history. Several batches may
qualify; none is chosen or promised.
-/
def AdmissibleNext (work : Work) (history : History) (batch : List WorkEvent) : Prop :=
  ValidHistory work history
  ∧ ¬AdmissibleRun work history
  ∧ batch ≠ []
  ∧ ValidHistory work { history with batches := history.batches ++ [batch] }

/-- Some terminal continuation retains the initial notices and every observed batch.
This optional progress property does not restrict ValidHistory or AdmissibleNext.
-/
def History.CanFinish (history : History) (work : Work) : Prop :=
  ∃ suffix, AdmissibleRun work { history with batches := history.batches ++ suffix }

end WorkScheduler

namespace Execution

-----------------------------------------------------------------------------------------
-- Proposed WorkQueue invariants
-----------------------------------------------------------------------------------------

/-!
The pinned draft calls CreateWorkQueue but supplies no algorithm or complete invariant
contract for it. The premises in this section are our proposed semantic contract, and
potential contributions to the specification, not claims about existing normative text.

Section 7 still constrains observable responses (identity, references, completion, paths).
Those response properties are conclusions to derive, not scheduler admission filters.

AccountsForWork uses the independent relations above. Its proposed accounting rules
combine draft-derived constraints with gap-filling choices:

- one-shot value publication and node termination, with open-owner failure occurrences;
- producer dependencies and in-order publication of items within each stream;
- ancestry/owner-aware release and alternative initial/later notice frontiers;
- one permitted longest-path owner for a shared value, allowing owner ties;
- failure/cancellation propagation and termination only after work is accounted for.

Longest-path owner selection reflects Section 7's object-result rule; the precise internal
release, dependency, and cancellation conditions complete the undefined queue interface.

History matching is a finite presentation of these rules. Implementations need not store
its witnesses, select FIFO order, or realize every permitted choice. The contract admits
stalled prefixes and imposes no fairness or host-future termination assumption. Its
adequacy and minimality remain review/proof questions; none is established just by
defining Conforms.
-/

section WorkQueueInvariants

/-- Project source observations into the independently specified work-history vocabulary.
-/
def WorkQueueResult.toHistory (result : WorkQueueResult) (batches : List (List WorkEvent))
    : GraphQL.IncrementalDelivery.WorkScheduler.History :=
  {
    initialGroups := result.initialGroups,
    initialStreams := result.initialStreams,
    batches
  }

/-- The source starts with no observed outputs and admits that empty history, excluding a
vacuously impossible source.
-/
def WorkQueueResult.Initialized (result : WorkQueueResult) : Prop :=
  result.workEventStream.history = [] ∧ result.workEventStream.admissible []

/-- Every prefix of an admitted source history is also admitted. -/
def WorkQueueResult.PrefixClosed (result : WorkQueueResult) : Prop :=
  ∀ before after,
    before.IsPrefix after
    → result.workEventStream.admissible after
    → result.workEventStream.admissible before

/-- Every admitted source history obeys the independent work-accounting relation. No
wire-response correctness property is assumed.
-/
def WorkQueueResult.AccountsForWork (result : WorkQueueResult) (work : Work) : Prop :=
  ∀ batches,
    result.workEventStream.admissible batches
    → GraphQL.IncrementalDelivery.WorkScheduler.ValidHistory work
        (result.toHistory batches)

/-- Finished source histories are exactly admitted terminal work runs; eventual
termination is not promised.
-/
def WorkQueueResult.TerminationMatchesWork (result : WorkQueueResult) (work : Work)
    : Prop :=
  ∀ batches,
    result.workEventStream.finished batches
    ↔ result.workEventStream.admissible batches
      ∧ GraphQL.IncrementalDelivery.WorkScheduler.AdmissibleRun work
          (result.toHistory batches)

/-- The queue result satisfies initialization, prefix closure, work accounting, and
termination requirements for the submitted work.
-/
def WorkQueueResult.Conforms (result : WorkQueueResult) (work : Work) : Prop :=
  result.Initialized
  ∧ result.PrefixClosed
  ∧ result.AccountsForWork work
  ∧ result.TerminationMatchesWork work

/-- The factory's result conforms for the submitted work. Empty work never calls
CreateWorkQueue and imposes no requirement on the scheduler.
-/
def WorkScheduler.Conforms (scheduler : WorkScheduler) (work : Work) : Prop :=
  work.size ≠ 0 → (scheduler.createWorkQueue work).Conforms work

end WorkQueueInvariants

-----------------------------------------------------------------------------------------
-- Optional implementation progress, separate from the conformance contract
-----------------------------------------------------------------------------------------

/-- Every admitted batch history has a finished continuation in the same source language.
This is finite nonblocking, not fairness or eventual host execution, and is not required
by Conforms. Initialization is still needed to exclude an empty source language.
-/
def WorkQueueResult.Nonblocking (result : WorkQueueResult) : Prop :=
  ∀ batches,
    result.workEventStream.admissible batches
    → ∃ suffix, result.workEventStream.finished (batches ++ suffix)

end Execution

-----------------------------------------------------------------------------------------
-- Maximal sources for the proposed contract
-----------------------------------------------------------------------------------------

/-!
These definitions expose the contract's alternatives; they do not choose a completion
order. Initialization remains an explicit caller-supplied choice. The proof module
WorkScheduler/SpecificationSource proves conformance for valid initial notices.
-/

namespace WorkScheduler

/-- Maximal source language for a chosen initialization. Matching and failure cuts remain
existential evidence in AdmissiblePrefix/Run; the source stores only observations. Invalid
initial notices are rejected by Conforms, not silently repaired here.
-/
def specificationSource (work : Work) (groups streams : List DeliveryNode)
    : WorkQueueResult :=
  let history :=
    fun batches =>
      { initialGroups := groups, initialStreams := streams, batches : History }
  {
    initialGroups := groups,
    initialStreams := streams,
    workEventStream :=
      {
        admissible :=
          fun batches => ValidHistory work (history batches),
        finished := fun batches => AdmissibleRun work (history batches)
      }
  }

/-- Initialization remains an explicit choice; subsequent observations remain relational.
There is no default initialization policy or selected future completion order.
-/
def specificationScheduler (initialNotices : Work → List DeliveryNode × List DeliveryNode)
    : Execution.WorkScheduler :=
  ⟨fun work =>
    let (groups, streams) := initialNotices work
    specificationSource work groups streams⟩

end WorkScheduler
end GraphQL.IncrementalDelivery
