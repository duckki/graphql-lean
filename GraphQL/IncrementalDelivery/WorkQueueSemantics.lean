import GraphQL.IncrementalDelivery.Execution

/-! Output-history semantics for the finite pure-outcome model.
Admission relates Work to observations, not to an internal queue, graph, or progress
machine. Structural occurrences distinguish equal payloads and shared work. Existential
publication matching and failure cuts explain a history; neither selects its future.

Read EventAllowed for the event rules. Its helpers answer three questions: what work
exists, what has been observed, and what failures justify cancellation. They describe
work and its observations, not runtime workers or internal queue state. Observed
owners are effective publication owners after any implementation-specific normalization;
the contract is not imposed directly on provisional owners in a concrete raw queue.
-/

namespace GraphQL.IncrementalDelivery
open GraphQL.IncrementalDelivery.Execution

namespace WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- What work exists?
-----------------------------------------------------------------------------------------

/-- Ordered delivery-node refs; distinct from task occurrences and allocated wire IDs. -/
abbrev NodeRefs := List NodeRef

inductive NodeKind where
  | group
  | stream
deriving Repr, BEq, DecidableEq

/-- A structural route through Work; unrelated to a response path or delivery-node ref. -/
abbrev Address := List Nat

/-- Addresses are structural positions in Work, not allocated runtime task IDs. -/
inductive Occurrence where
  /-- One execution-group task from the spec's `Work.tasks` collection. -/
  | executionGroup (address : Address)
  | item (address : Address) (index : Nat)
deriving Repr, BEq, DecidableEq

inductive Payload where
  | object (path : ResponsePath) (result : Result (List (Name × ResponseValue)))
  | item (node : DeliveryNode) (result : Result ResponseValue)
deriving Repr

def Payload.failure : Payload → Option Nat
  | .object _ (.error errors) | .item _ (.error errors) => some errors
  | _ => none

/-- A view of existing work and its context, not a task graph or queue state. -/
structure WorkLocation where
  current : Work
  producer : Option Occurrence
  owners : NodeRefs

/-- Descend one structural edge, retaining the absolute address of any producer. -/
def WorkLocation.child? (location : WorkLocation) (address : Address) (index : Nat)
    : Option WorkLocation :=
  match location.current, index with
  | .combine left _, 0 => some { location with current := left }
  | .combine _ right, 1 => some { location with current := right }
  | .executionGroup groups _ _ children, 0 =>
      some
        ⟨
          children,
          some (.executionGroup address),
          groups.map (fun group => group.node.ref)
        ⟩
  | .stream _ items, index =>
      items[index]?.map (fun entry => ⟨entry.2, some (.item address index), []⟩)
  | _, _ => none

/-- Follow an address in work; invalid edges have no location. No refs are deduplicated.
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

/-- The address identifies this subwork, generating task, and enclosing defer refs. -/
def Located (root : Work) (address : Address) (current : Work)
    (producer : Option Occurrence) (owners : NodeRefs)
    : Prop :=
  locateWork root address = some ⟨current, producer, owners⟩

/-- The structural occurrence identifies a task with these owners, producer, and payload.
-/
def TaskAt (work : Work) (occurrence : Occurrence) (owners : NodeRefs)
    (producer : Option Occurrence) (payload : Payload)
    : Prop :=
  match occurrence with
  | .executionGroup address =>
      ∃ groups path result children enclosing,
        Located work address (.executionGroup groups path result children) producer
          enclosing
        ∧ owners = groups.map (fun group => group.node.ref)
        ∧ payload = .object path result
  | .item address index =>
      ∃ node items enclosing result children,
        Located work address (.stream node items) producer enclosing
        ∧ items[index]? = some (result, children)
        ∧ owners = [node.ref]
        ∧ payload = .item node result

/-- Some location contains this node descriptor. Dependencies are defer ancestors for a
group and enclosing defer owners for a stream; they are never structural producers.
Repeated refs retain every descriptor.
-/
def NodeAt (work : Work) (node : DeliveryNode) (kind : NodeKind) (dependencies : NodeRefs)
    (producer : Option Occurrence)
    : Prop :=
  match kind with
  | .group =>
      ∃ address groups path result children enclosing group,
        Located work address (.executionGroup groups path result children) producer
          enclosing
        ∧ group ∈ groups
        ∧ node = group.node
        ∧ dependencies = group.ancestors.map DeliveryNode.ref
  | .stream =>
      ∃ address items, Located work address (.stream node items) producer dependencies

/-- The task has exactly this list of contributing owner refs. -/
def TaskHasOwners (work : Work) (occurrence : Occurrence) (owners : NodeRefs) : Prop :=
  ∃ producer payload, TaskAt work occurrence owners producer payload

/-- The task has this generating occurrence, or is a root task when producer is none. -/
def TaskHasProducer (work : Work) (occurrence : Occurrence) (producer : Option Occurrence)
    : Prop :=
  ∃ owners payload, TaskAt work occurrence owners producer payload

/-- The task's fixed outcome is successful; this does not assert publication. -/
def TaskSucceeds (work : Work) (occurrence : Occurrence) : Prop :=
  ∃ owners producer payload,
    TaskAt work occurrence owners producer payload ∧ payload.failure = none

/-- Some descriptor with this ref and kind has these release dependencies. -/
def NodeHasDependencies (work : Work) (ref : NodeRef) (kind : NodeKind)
    (dependencies : NodeRefs)
    : Prop :=
  ∃ node producer, NodeAt work node kind dependencies producer ∧ node.ref = ref

/-- Some descriptor with this ref has this producer; repeated descriptors are retained. -/
def NodeHasProducer (work : Work) (ref : NodeRef) (producer : Option Occurrence) : Prop :=
  ∃ node kind dependencies, NodeAt work node kind dependencies producer ∧ node.ref = ref

/-- (Reachable work occurrence) derives a successful producer chain for the occurrence. -/
inductive Reachable (work : Work) : Occurrence → Prop where
  | root {occurrence} (known : TaskHasProducer work occurrence none)
    : Reachable work occurrence
  | child {occurrence producer}
    (known : TaskHasProducer work occurrence (some producer))
    (success : TaskSucceeds work producer) (reachable : Reachable work producer)
    : Reachable work occurrence

-----------------------------------------------------------------------------------------
-- Which failures justify cancellation?
-----------------------------------------------------------------------------------------

/-- Accepted failure settlements in order, each paired with the preceding output count.
Equal cuts retain settlement order; cuts are not notification positions or host times.
-/
abbrev FailureCuts := List (Nat × Occurrence)

/-! Failure settlement and notification have different eligibility rules. A task can
settle after a previously announced owner has closed, while an unannounced shared owner
still keeps it alive. Failure cuts retain accepted settlement order; they do not delay
settlement until a reporting owner is open. Cut i is after initialization and before
output i. Real failing work with successful producers must have a previously announced
contributing owner and be uncancelled by earlier settlements. Notification still requires
an open owner in EventAllowed.

At each cut, already published occurrences are protected from cancellation. The
observable relations retain consequences reached at each cut, so later publications
cannot undo earlier cancellation. Later cancellation also does not erase an accepted
failure from the error inventory: FailureWitness licenses it against earlier settlements,
not against failures that settle afterward but are notified sooner.
-/

namespace Causality

mutual
  /-- Node failure is the least closure of task failures and dependencies, relative to
  publications already visible at one failure cut.
  -/
  inductive NodeFailed (work : Work) (failed : List Occurrence)
      (published : Occurrence → Prop)
      : NodeRef → Prop where
    | task {occurrence owners ref} (known : TaskHasOwners work occurrence owners)
      (owner : ref ∈ owners) (finished : occurrence ∈ failed)
      : NodeFailed work failed published ref
    | groupDependency {ref dependencies dependency}
      (known : NodeHasDependencies work ref .group dependencies)
      (member : dependency ∈ dependencies)
      (failure : NodeFailed work failed published dependency)
      : NodeFailed work failed published ref
    | streamDependencies {ref dependencies}
      (known : NodeHasDependencies work ref .stream dependencies)
      (nonempty : dependencies ≠ [])
      (failures
        : ∀ dependency ∈ dependencies, NodeFailed work failed published dependency)
      : NodeFailed work failed published ref
    /-- Every descriptor's producer is unavailable; any root descriptor blocks this rule.
    -/
    | producers {ref} (known : ∃ producer, NodeHasProducer work ref producer)
      (noRoot : ¬NodeHasProducer work ref none)
      (unpublished
        : ∀ producer, NodeHasProducer work ref (some producer) → ¬published producer)
      (cancelled
        : ∀ producer,
            NodeHasProducer work ref (some producer)
            → producer ∉ failed
            → TaskCancelled work failed published producer)
      : NodeFailed work failed published ref

  /-- A task is cancelled only if it was unpublished at this failure cut. The least
  relation excludes self-justifying causal cycles.
  -/
  inductive TaskCancelled (work : Work) (failed : List Occurrence)
      (published : Occurrence → Prop)
      : Occurrence → Prop where
    | owners {occurrence owners} (known : TaskHasOwners work occurrence owners)
      (unpublished : ¬published occurrence)
      (nonempty : owners ≠ [])
      (failures : ∀ ref ∈ owners, NodeFailed work failed published ref)
      : TaskCancelled work failed published occurrence
    | producerFailed {occurrence producer}
      (known : TaskHasProducer work occurrence (some producer))
      (unpublished : ¬published occurrence)
      (failure : producer ∈ failed)
      : TaskCancelled work failed published occurrence
    | producerCancelled {occurrence producer}
      (known : TaskHasProducer work occurrence (some producer))
      (unpublished : ¬published occurrence)
      (cancelled : TaskCancelled work failed published producer)
      : TaskCancelled work failed published occurrence
end

end Causality

/-- Accepted failures settled through `cut`, whether or not their owners have reported.
Later cancellation does not remove an earlier accepted settlement from this inventory.
-/
def failedBefore (failures : FailureCuts) (cut : Nat) : List Occurrence :=
  (failures.filter (fun entry => entry.1 ≤ cut)).map Prod.snd

-----------------------------------------------------------------------------------------
-- What has been observed?
-----------------------------------------------------------------------------------------

/-- Maps zero-based unbatched work-event indices to producing work occurrences.
Indices precede grouping or batching; only value-publication indices are used.
-/
abbrev PublicationMatching := Nat → Occurrence

def eventPending : WorkQueueEvent → NodeRefs
  | .groupSuccess _ groups streams | .streamValues _ _ groups streams =>
      (groups ++ streams).map DeliveryNode.ref
  | _ => []

def eventCompleted : WorkQueueEvent → NodeRefs
  | .groupSuccess node ..
  | .groupFailure node _
  | .streamSuccess node
  | .streamFailure node _ => [node.ref]
  | _ => []

/-- References introduced by pending notices in the supplied work-event history.
This is not the set of nodes still open at the end of that history.
-/
def pendingRefs (events : List WorkQueueEvent) : NodeRefs := events.flatMap eventPending

/-- References closed by completion notices in the supplied work-event history. -/
def completedRefs (events : List WorkQueueEvent) : NodeRefs :=
  events.flatMap eventCompleted

/-- (IsValue event) classifies the supplied work event as a value publication rather than
control.
-/
def IsValue : WorkQueueEvent → Prop
  | .groupValues .. | .streamValues .. => True
  | _ => False

/-- The occurrence has a value publication in the observed prefix, identified by the
matching shared across the entire history.
-/
def Published (matching : PublicationMatching) (events : List WorkQueueEvent)
    (occurrence : Occurrence)
    : Prop :=
  ∃ index event, events[index]? = some event ∧ IsValue event ∧ matching index = occurrence

/-- A node has failed at some reached failure cut. Each cut uses only publications
visible before that cut, so a later owner failure cannot retroactively cancel a
producer whose value was already published. Earlier failure consequences persist as
the output history grows.
-/
def NodeFailed (work : Work) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts) (ref : NodeRef)
    : Prop :=
  ∃ cut,
    cut ∈ failures.map Prod.fst
    ∧ cut ≤ events.length
    ∧ Causality.NodeFailed work (failedBefore failures cut)
        (Published matching (events.take cut)) ref

/-- A task was cancelled at some reached failure cut while still unpublished. A
later publication cannot be used to erase this historical cancellation.
-/
def TaskCancelled (work : Work) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts) (occurrence : Occurrence)
    : Prop :=
  ∃ cut,
    cut ∈ failures.map Prod.fst
    ∧ cut ≤ events.length
    ∧ Causality.TaskCancelled work (failedBefore failures cut)
        (Published matching (events.take cut)) occurrence

/-- Initially announced references followed by announcements in the work-event history. -/
def announcedRefs (initial : NodeRefs) (events : List WorkQueueEvent) : NodeRefs :=
  initial ++ pendingRefs events

/-- The node ref has been announced initially or in the output prefix, but not yet closed.
-/
def Open (initial : NodeRefs) (events : List WorkQueueEvent) (ref : NodeRef) : Prop :=
  ref ∈ announcedRefs initial events ∧ ref ∉ completedRefs events

/-- Ordered accepted settlements of reachable failures, licensed against earlier failures.
Some contributing owner must have been announced by the settlement cut, but it may already
have closed. This permits an already-started shared task to settle through a still-healthy
latent owner. The uncancelled premise remains mandatory; prior announcement alone does
not keep fully invalidated work alive. Work with no announced owner cannot fail silently.

Completion events separately require an open owner and count failures settled by their
own boundary. Earlier completions are not retroactively charged for later settlements.
Every cut is bounded by the observed output length. In an explained history, failed
occurrences remain unique: an earlier copy cancels the unpublished task through its owners.
-/
def FailureWitness (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts)
    : Prop :=
  ∀ before cut occurrence after,
    failures = before ++ (cut, occurrence) :: after
    → cut ≤ events.length
      ∧ (∀ earlier ∈ before, earlier.1 ≤ cut)
      ∧ (∃ owners producer payload,
          TaskAt work occurrence owners producer payload
          ∧ payload.failure.isSome = true
          ∧ Reachable work occurrence
          ∧ ∃ ref ∈ owners, ref ∈ announcedRefs initial (events.take cut))
      ∧ ¬TaskCancelled work matching (events.take cut) before occurrence

-----------------------------------------------------------------------------------------
-- Which events are permitted?
-----------------------------------------------------------------------------------------

/-! EventAllowed combines publication readiness, contributing-owner choice, and fresh
announcements. Successful closure additionally accounts for every contributing task.
-/

/-- The task occurrence has been published or causally cancelled by known failures. -/
def TaskAccounted (work : Work) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts) (occurrence : Occurrence)
    : Prop :=
  TaskCancelled work matching events failures occurrence
  ∨ Published matching events occurrence

/-- Every task contributing to the node ref has been published or cancelled. -/
def NodeAccounted (work : Work) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts) (ref : NodeRef)
    : Prop :=
  ∀ occurrence owners,
    TaskHasOwners work occurrence owners
    → ref ∈ owners
    → TaskAccounted work matching events failures occurrence

/-- The node ref has not failed and is absent, completed, or unannounced with all
contributing tasks accounted for.
-/
def DependencySatisfied (work : Work) (initial : NodeRefs)
    (matching : PublicationMatching) (events : List WorkQueueEvent)
    (failures : FailureCuts) (ref : NodeRef)
    : Prop :=
  ¬NodeFailed work matching events failures ref
  ∧ ((¬∃ producer, NodeHasProducer work ref producer)
      ∨ ref ∈ completedRefs events
      ∨ ref ∉ announcedRefs initial events
        ∧ NodeAccounted work matching events failures ref)

/-- Some task contributing to this ref has a recorded failure through `cut`, an
unbatched output-prefix length. Failure licensing remains in `FailureWitness`.
-/
def HasRecordedFailure (work : Work) (failures : FailureCuts) (cut : Nat) (ref : NodeRef)
    : Prop :=
  ∃ occurrence owners,
    occurrence ∈ failedBefore failures cut
    ∧ TaskHasOwners work occurrence owners
    ∧ ref ∈ owners

/-- A fresh node can be announced after its producer publishes and its dependencies
are satisfied. Groups may also be announced to report a recorded contributing failure;
this does not make them healthy publication supporters or permit child release. A failed
but open group can still supply the effective ID for a shared value supported elsewhere.
-/
def CanAnnounce (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts) (node : DeliveryNode)
    (kind : NodeKind) (dependencies : NodeRefs) (producer : Option Occurrence)
    : Prop :=
  node.ref ∉ announcedRefs initial events
  ∧ ((¬NodeFailed work matching events failures node.ref
        ∧ (kind = .stream ∨ ¬NodeAccounted work matching events failures node.ref))
      ∨ (kind = .group ∧ HasRecordedFailure work failures events.length node.ref))
  ∧ (∀ source, producer = some source → Published matching events source)
  ∧ match kind with
    | .group =>
        ∀ ref ∈ dependencies,
          DependencySatisfied work initial matching events failures ref
    | .stream =>
        dependencies = []
        ∨ ∃ ref ∈ dependencies,
            DependencySatisfied work initial matching events failures ref

/-- Fresh, distinct group and stream notices whose nodes are eligible after the observed
prefix.
-/
def Announcements (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts)
    (groups streams : List DeliveryNode)
    : Prop :=
  ((groups ++ streams).map DeliveryNode.ref).Nodup
  ∧ (∀ group ∈ groups,
      ∃ dependencies producer,
        NodeAt work group .group dependencies producer
        ∧ CanAnnounce work initial matching events failures group .group dependencies
            producer)
  ∧ (∀ stream ∈ streams,
      ∃ dependencies producer,
        NodeAt work stream .stream dependencies producer
        ∧ CanAnnounce work initial matching events failures stream .stream dependencies
            producer)

/-- A nonempty initial frontier of eligible group and stream notices. -/
def Initializes (work : Work) (groups streams : List DeliveryNode) : Prop :=
  Announcements work [] (fun _ => .executionGroup []) [] [] groups streams
  ∧ groups ++ streams ≠ []

/-- The candidate is a known contributing owner with an announced, still-open notice.
This is wire-ID eligibility only; it does not require or establish healthy support.
-/
def OpenOwner (work : Work) (initial : NodeRefs) (events : List WorkQueueEvent)
    (owners : NodeRefs) (node : DeliveryNode)
    : Prop :=
  (∃ kind dependencies producer, NodeAt work node kind dependencies producer)
  ∧ node.ref ∈ owners
  ∧ Open initial events node.ref

/-- A known open contributor can support publication when it has not failed. -/
def HealthyOpenOwner (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts) (owners : NodeRefs)
    (node : DeliveryNode)
    : Prop :=
  OpenOwner work initial events owners node
  ∧ ¬NodeFailed work matching events failures node.ref

/-- A healthy open contributor supports publication; the effective wire owner is any
open contributor with a longest response path, allowing ties. The selected owner may have
a recorded failure of another shared task while its own completion is still pending.
Publisher normalization may select it instead of the healthy supporter. `CanPublish`
separately excludes cancelled tasks and checks publication dependencies.
-/
def PublicationOwner (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts) (owners : NodeRefs)
    (node : DeliveryNode)
    : Prop :=
  OpenOwner work initial events owners node
  ∧ (∃ supporter, HealthyOpenOwner work initial matching events failures owners supporter)
  ∧ ∀ other,
      OpenOwner work initial events owners other → other.path.length ≤ node.path.length

/-- The occurrence is unpublished and uncancelled, with its producer already published. A
noninitial stream item also requires publication of the preceding item.
-/
def CanPublish (work : Work) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts) (occurrence : Occurrence)
    (producer : Option Occurrence)
    : Prop :=
  ¬Published matching events occurrence
  ∧ ¬TaskCancelled work matching events failures occurrence
  ∧ (∀ source, producer = some source → Published matching events source)
  ∧ match occurrence with
    | .item address (index + 1) => Published matching events (.item address index)
    | _ => True

/-- The claimed error count sums supplied accepted failures contributing to the node ref.
Completion rules supply settlements through the event boundary, not notification order.
-/
def NodeErrors (work : Work) (failed : List Occurrence) (ref : NodeRef) (errors : Nat)
    : Prop :=
  ∃ contribution : Occurrence → Nat,
    (∀ occurrence ∈ failed,
      ∃ owners producer payload,
        TaskAt work occurrence owners producer payload
        ∧ contribution occurrence = if ref ∈ owners then payload.failure.getD 0 else 0)
    ∧ errors = (failed.map contribution).sum

/-- The next atomic event has valid provenance, dependencies, ownership, and notices
relative to the observed prefix and known failures. New notices follow the carrier.
All checks use only failure cuts at or before `before.length`. Notice eligibility
sees the carrier's publication or closure, but not failures recorded after that carrier.
Object contributor metadata is ignored here: `TaskAt` and `PublicationOwner` use the
original Work.
-/
def EventAllowed (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (before : List WorkQueueEvent) (failures : FailureCuts) (event : WorkQueueEvent)
    : Prop :=
  let failures := failures.filter (fun entry => entry.1 ≤ before.length)
  match event with
  | .groupValues node values =>
      ∃ owners producer value,
        values = [value]
        ∧ TaskAt work (matching before.length) owners producer
            (.object value.path (.ok (value.data, value.errors)))
        ∧ CanPublish work matching before failures (matching before.length) producer
        ∧ PublicationOwner work initial matching before failures owners node
  | .streamValues node values groups streams =>
      ∃ owners producer value,
        values = [value]
        ∧ TaskAt work (matching before.length) owners producer
            (.item node (.ok (value.item, value.errors)))
        ∧ CanPublish work matching before failures (matching before.length) producer
        ∧ PublicationOwner work initial matching before failures owners node
        ∧ Announcements work initial matching
            (before ++ [.streamValues node values [] []]) failures groups streams
  | .groupSuccess node groups streams =>
      (∃ dependencies producer, NodeAt work node .group dependencies producer)
      ∧ Open initial before node.ref
      ∧ ¬NodeFailed work matching before failures node.ref
      ∧ NodeAccounted work matching before failures node.ref
      ∧ Announcements work initial matching
          (before ++ [.groupSuccess node [] []]) failures groups streams
  | .streamSuccess node =>
      (∃ dependencies producer, NodeAt work node .stream dependencies producer)
      ∧ Open initial before node.ref
      ∧ ¬NodeFailed work matching before failures node.ref
      ∧ NodeAccounted work matching before failures node.ref
  | .groupFailure node errors =>
      (∃ dependencies producer, NodeAt work node .group dependencies producer)
      ∧ Open initial before node.ref
      ∧ NodeFailed work matching before failures node.ref
      ∧ NodeErrors work (failedBefore failures before.length) node.ref errors
  | .streamFailure node errors =>
      (∃ dependencies producer, NodeAt work node .stream dependencies producer)
      ∧ Open initial before node.ref
      ∧ NodeFailed work matching before failures node.ref
      ∧ NodeErrors work (failedBefore failures before.length) node.ref errors
  | .workQueueTermination => False

-----------------------------------------------------------------------------------------
-- Admitted histories and batching
-----------------------------------------------------------------------------------------

/-- Initial notices and atomic outputs follow the work rules under one publication
matching and bounded failure cuts. No wire correctness or eventual progress is assumed.
-/
def Explains (work : Work) (groups streams : List DeliveryNode)
    (events : List WorkQueueEvent) (matching : PublicationMatching)
    (failures : FailureCuts)
    : Prop :=
  Initializes work groups streams
  ∧ FailureWitness work ((groups ++ streams).map DeliveryNode.ref) matching events
      failures
  ∧ ∀ index event,
      events[index]? = some event
      → EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
          (events.take index) failures event

/-- All tasks are accounted for, and every node is closed or unannounced and failed or
accounted for.
-/
def Terminal (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failures : FailureCuts)
    : Prop :=
  (∀ occurrence owners producer payload,
    TaskAt work occurrence owners producer payload
    → TaskAccounted work matching events failures occurrence)
  ∧ ∀ node kind dependencies producer,
      NodeAt work node kind dependencies producer
      → node.ref ∈ completedRefs events
        ∨ node.ref ∉ announcedRefs initial events
          ∧ (NodeFailed work matching events failures node.ref
              ∨ NodeAccounted work matching events failures node.ref)

/-- Adjacent compatible value events may be represented by a single spec event with
multiple values. This is independent of work-event and response-event batching.
-/
def combineValues : WorkQueueEvent → WorkQueueEvent → Option WorkQueueEvent
  | .groupValues group left, .groupValues other right =>
      if group.ref == other.ref then some (.groupValues group (left ++ right)) else none
  | .streamValues stream left groups streams,
    .streamValues other right moreGroups moreStreams =>
      if stream.ref == other.ref then
        some
          (.streamValues stream (left ++ right) (groups ++ moreGroups)
            (streams ++ moreStreams))
      else
        none
  | _, _ => none

/-- (ValueGrouping events grouped) relates input atoms events to grouped outputs obtained
by optional adjacent compatible-value coalescing, preserving value order and contents.
-/
inductive ValueGrouping : List WorkQueueEvent → List WorkQueueEvent → Prop where
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
inductive WorkBatching : List WorkQueueEvent → List (List WorkQueueEvent) → Prop where
  | nil : WorkBatching [] []
  | cons {batch tail grouped rest}
    (nonempty : batch ≠ [])
    (values : ValueGrouping batch grouped)
    (subsequent : WorkBatching tail rest)
    : WorkBatching (batch ++ tail) (grouped :: rest)

structure History where
  initialGroups : List DeliveryNode
  initialStreams : List DeliveryNode
  batches : List (List WorkQueueEvent)
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
        ((history.initialGroups ++ history.initialStreams).map DeliveryNode.ref) matching
        events failures
    ∧ WorkBatching (events ++ [.workQueueTermination]) history.batches

/-- An admitted prefix or terminal run. -/
def ValidHistory (work : Work) (history : History) : Prop :=
  AdmissiblePrefix work history ∨ AdmissibleRun work history

/-- A nonempty batch may extend the valid, nonterminal history. Several batches may
qualify; none is chosen or promised.
-/
def AdmissibleNext (work : Work) (history : History) (batch : List WorkQueueEvent)
    : Prop :=
  ValidHistory work history
  ∧ ¬AdmissibleRun work history
  ∧ batch ≠ []
  ∧ ValidHistory work { history with batches := history.batches ++ [batch] }

/-- Some terminal continuation retains the initial notices and every observed batch.
This optional progress property does not restrict ValidHistory or AdmissibleNext.
-/
def History.CanFinish (history : History) (work : Work) : Prop :=
  ∃ suffix, AdmissibleRun work { history with batches := history.batches ++ suffix }

end WorkQueueSemantics

namespace Execution

-----------------------------------------------------------------------------------------
-- Proposed WorkQueue invariants
-----------------------------------------------------------------------------------------

/-!
The pinned draft calls CreateWorkQueue but supplies no algorithm or complete invariant
contract for it. The premises in this section are our proposed semantic contract, and
potential contributions to the specification, not claims about existing normative text.

Section 7 still constrains observable responses (identity, references, completion, paths).
Those response properties are conclusions to derive, not queue admission filters.

AccountsForWork uses the independent relations above. Its proposed accounting rules
combine draft-derived constraints with gap-filling choices:

- one-shot value publication and node termination, with open-owner completion events;
- producer dependencies and in-order publication of items within each stream;
- ancestry/owner-aware release and alternative initial/later notice frontiers;
- healthy open publication support and a longest open wire owner, allowing owner ties;
- accepted failures with a previously announced owner and no earlier cancellation;
- failure/cancellation propagation and termination only after work is accounted for.

Longest-path owner selection reflects Section 7's object-result rule; the precise internal
release, dependency, and cancellation conditions complete the undefined queue interface.
The healthy supporter and the selected wire owner need not be the same contributor:
a failed but still-open co-owner may have the longest path for another successful task.

History matching is a finite presentation of these rules. Implementations need not store
its witnesses, select FIFO order, or realize every permitted choice. The contract admits
stalled prefixes and imposes no fairness or host-future termination assumption. Its
adequacy and minimality remain review/proof questions; none is established just by
defining Conforms.
-/

section WorkQueueInvariants

/-- The source starts with no observed outputs and admits that empty history, excluding a
vacuously impossible source.
-/
def WorkQueue.Initialized (result : WorkQueue) : Prop :=
  result.workEventStream.history = [] ∧ result.workEventStream.admissible []

/-- Every prefix of an admitted source history is also admitted. -/
def WorkQueue.PrefixClosed (result : WorkQueue) : Prop :=
  ∀ before after,
    before.IsPrefix after
    → result.workEventStream.admissible after
    → result.workEventStream.admissible before

/-- Every admitted batch list, paired with this queue's initial notices, obeys the
independent work-accounting relation. No wire-response correctness property is assumed.
-/
def WorkQueue.AccountsForWork (result : WorkQueue) (work : Work) : Prop :=
  ∀ batches,
    result.workEventStream.admissible batches
    → GraphQL.IncrementalDelivery.WorkQueueSemantics.ValidHistory work
        ⟨result.initialGroups, result.initialStreams, batches⟩

/-- Finished source histories are exactly admitted terminal work runs; eventual
termination is not promised.
-/
def WorkQueue.TerminationMatchesWork (result : WorkQueue) (work : Work) : Prop :=
  ∀ batches,
    result.workEventStream.finished batches
    ↔ result.workEventStream.admissible batches
      ∧ GraphQL.IncrementalDelivery.WorkQueueSemantics.AdmissibleRun work
          ⟨result.initialGroups, result.initialStreams, batches⟩

/-- The queue interface satisfies initialization, prefix closure, work accounting, and
termination requirements for the submitted work.
-/
def WorkQueue.Conforms (result : WorkQueue) (work : Work) : Prop :=
  result.Initialized
  ∧ result.PrefixClosed
  ∧ result.AccountsForWork work
  ∧ result.TerminationMatchesWork work

end WorkQueueInvariants

-----------------------------------------------------------------------------------------
-- Optional implementation progress, separate from the conformance contract
-----------------------------------------------------------------------------------------

/-- Every admitted batch history has a finished continuation in the same source language.
This is finite nonblocking, not fairness or eventual host execution, and is not required
by Conforms. Initialization is still needed to exclude an empty source language.
-/
def WorkQueue.Nonblocking (result : WorkQueue) : Prop :=
  ∀ batches,
    result.workEventStream.admissible batches
    → ∃ suffix, result.workEventStream.finished (batches ++ suffix)

end Execution

end GraphQL.IncrementalDelivery
