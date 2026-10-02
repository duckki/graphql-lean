import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskMemberships

/-! Agreement between the publisher registry and open notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Publisher active nodes and abstract open notices
-----------------------------------------------------------------------------------------

/-- The publisher's active-node registry names exactly the announced, uncompleted
keys in the normalized output history. This is a proof invariant, not a field of
the executable publisher.
-/
def IncrementalPublisher.RegistryMatchesOpen
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    : Prop :=
  ∀ key, key ∈ publisher.active.map Execution.DeliveryNode.key ↔ Open initial events key

/-- The publisher begins with precisely the initial open notices. -/
theorem IncrementalPublisher.registry_initial (nodes : List Execution.DeliveryNode)
    : ({ active := nodes } : IncrementalPublisher).RegistryMatchesOpen
        (nodes.map Execution.DeliveryNode.key) [] := by
  intro key
  simp [Open, announcedKeys, pendingKeys, completedKeys]

/-- Filtering a closed key from the active list removes exactly that key. -/
private theorem activeKeys_filter_closed
    (nodes : List Execution.DeliveryNode) (closed key : Nat)
    : key ∈ (nodes.filter (fun node => node.key != closed)).map Execution.DeliveryNode.key
      ↔ key ∈ nodes.map Execution.DeliveryNode.key ∧ key ≠ closed := by
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨node, ⟨member, different⟩, rfl⟩
    exact ⟨⟨node, member, rfl⟩, by simpa using different⟩
  · rintro ⟨⟨node, member, rfl⟩, different⟩
    exact ⟨node, ⟨member, by simpa using different⟩, rfl⟩

/-- Any normalized closure with no new notices removes precisely the closed key
from abstract openness.
-/
private theorem open_append_closure
    (initial : Keys) (events : List Execution.WorkQueueEvent)
    (event : Execution.WorkQueueEvent) (closed key : Nat)
    (noPending : eventPending event = [])
    (completed : eventCompleted event = [closed])
    : Open initial (events ++ [event]) key ↔ Open initial events key ∧ key ≠ closed := by
  simp [Open, announcedKeys, pendingKeys, completedKeys,
    List.flatMap_append, noPending, completed, and_assoc]

/-- A closure-only output preserves active/open agreement. The witness is the
publisher's key filter and the abstract completion-key append.
-/
theorem IncrementalPublisher.registry_after_closure
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent) (event : Execution.WorkQueueEvent)
    (closed : Nat)
    (registry : publisher.RegistryMatchesOpen initial events)
    (noPending : eventPending event = [])
    (completed : eventCompleted event = [closed])
    : ({
        publisher with
          active :=
            (publisher.active.filter (fun node => node.key != closed))
      }).RegistryMatchesOpen
        initial (events ++ [event]) := by
  intro key
  rw [activeKeys_filter_closed, registry]
  exact (open_append_closure initial events event closed key noPending completed).symm

/-- GraphQL.js group-failure processing removes exactly its completed notice. -/
theorem IncrementalPublisher.registry_groupFailure
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (group : Execution.DeliveryNode) (errors : Nat)
    (registry : publisher.RegistryMatchesOpen initial events)
    : ((publisher.handleWorkQueueEvent
          (.groupFailure group errors)).1).RegistryMatchesOpen
        initial
        (events ++ (publisher.handleWorkQueueEvent (.groupFailure group errors)).2) := by
  change ({ publisher with active :=
      publisher.active.filter (fun node => node.key != group.key) }).RegistryMatchesOpen
    initial (events ++ [Execution.WorkQueueEvent.groupFailure group errors])
  exact publisher.registry_after_closure initial events _ group.key registry rfl rfl

/-- GraphQL.js stream-success processing removes exactly its completed notice. -/
theorem IncrementalPublisher.registry_streamSuccess
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (stream : Execution.DeliveryNode)
    (registry : publisher.RegistryMatchesOpen initial events)
    : ((publisher.handleWorkQueueEvent (.streamSuccess stream)).1).RegistryMatchesOpen
        initial
        (events ++ (publisher.handleWorkQueueEvent (.streamSuccess stream)).2) := by
  change ({ publisher with active :=
      publisher.active.filter (fun node => node.key != stream.key) }).RegistryMatchesOpen
    initial (events ++ [Execution.WorkQueueEvent.streamSuccess stream])
  exact publisher.registry_after_closure initial events _ stream.key registry rfl rfl

/-- GraphQL.js stream-failure processing removes exactly its completed notice. -/
theorem IncrementalPublisher.registry_streamFailure
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (stream : Execution.DeliveryNode) (errors : Nat)
    (registry : publisher.RegistryMatchesOpen initial events)
    : ((publisher.handleWorkQueueEvent
          (.streamFailure stream errors)).1).RegistryMatchesOpen
        initial
        (events
          ++ (publisher.handleWorkQueueEvent (.streamFailure stream errors)).2) := by
  change ({ publisher with active :=
      publisher.active.filter (fun node => node.key != stream.key) }).RegistryMatchesOpen
    initial (events ++ [Execution.WorkQueueEvent.streamFailure stream errors])
  exact publisher.registry_after_closure initial events _ stream.key registry rfl rfl

/-- A completion that also announces new nodes preserves the active/open
equation when those new keys were not previously completed and are not the
key being closed.
-/
private theorem open_append_announce_close
    (initial : Keys) (events : List Execution.WorkQueueEvent)
    (event : Execution.WorkQueueEvent) (newKeys : Keys) (closed key : Nat)
    (pending : eventPending event = newKeys)
    (completed : eventCompleted event = [closed])
    (fresh : ∀ newKey ∈ newKeys, newKey ∉ completedKeys events ∧ newKey ≠ closed)
    : Open initial (events ++ [event]) key
      ↔ (Open initial events key ∧ key ≠ closed) ∨ key ∈ newKeys := by
  have pendingEq : pendingKeys (events ++ [event])
      = pendingKeys events ++ newKeys := by
    simp [pendingKeys, List.flatMap_append, pending]
  have completedEq : completedKeys (events ++ [event])
      = completedKeys events ++ [closed] := by
    simp [completedKeys, List.flatMap_append, completed]
  simp only [Open, announcedKeys, pendingEq, completedEq,
    List.mem_append, List.mem_singleton, not_or]
  constructor
  · rintro ⟨announced, notOld, notClosed⟩
    rcases announced with initialMember | oldOrNew
    · exact Or.inl ⟨⟨Or.inl initialMember, notOld⟩, notClosed⟩
    · rcases oldOrNew with oldMember | newMember
      · exact Or.inl ⟨⟨Or.inr oldMember, notOld⟩, notClosed⟩
      · exact Or.inr newMember
  · rintro (⟨⟨announced, notOld⟩, notClosed⟩ | newMember)
    · rcases announced with initialMember | oldMember
      · exact ⟨Or.inl initialMember, notOld, notClosed⟩
      · exact ⟨Or.inr (Or.inl oldMember), notOld, notClosed⟩
    · obtain ⟨notOld, notClosed⟩ := fresh key newMember
      exact ⟨Or.inr (Or.inr newMember), notOld, notClosed⟩

/-- Group success keeps exactly the old open keys other than its own, together
with fresh child notices. This is the publisher-side registry transition.
-/
theorem IncrementalPublisher.registry_groupSuccess
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (group : Execution.DeliveryNode)
    (groups streams : List Execution.DeliveryNode)
    (registry : publisher.RegistryMatchesOpen initial events)
    (fresh
      : ∀ key ∈ (groups ++ streams).map Execution.DeliveryNode.key,
          key ∉ completedKeys events ∧ key ≠ group.key)
    : ((publisher.handleWorkQueueEvent
          (.groupSuccess group groups streams)).1).RegistryMatchesOpen
        initial
        (events
          ++ (publisher.handleWorkQueueEvent
                (.groupSuccess group groups streams)).2) := by
  intro key
  change key ∈
      ((publisher.active.filter (fun node => node.key != group.key))
          ++ groups ++ streams).map Execution.DeliveryNode.key
    ↔ Open initial
        (events ++ [Execution.WorkQueueEvent.groupSuccess group groups streams]) key
  simp only [List.map_append, List.mem_append, activeKeys_filter_closed]
  rw [registry]
  have bridge := open_append_announce_close initial events
    (.groupSuccess group groups streams)
    ((groups ++ streams).map Execution.DeliveryNode.key) group.key key
    rfl rfl fresh
  simpa only [List.map_append, List.mem_append, or_assoc] using bridge.symm

/-- An announcement-only event adds precisely its fresh child keys to abstract
openness; earlier completed keys cannot be reintroduced.
-/
private theorem open_append_announcement
    (initial : Keys) (events : List Execution.WorkQueueEvent)
    (event : Execution.WorkQueueEvent) (newKeys : Keys) (key : Nat)
    (pending : eventPending event = newKeys)
    (noCompletion : eventCompleted event = [])
    (fresh : ∀ newKey ∈ newKeys, newKey ∉ completedKeys events)
    : Open initial (events ++ [event]) key ↔ Open initial events key ∨ key ∈ newKeys := by
  have pendingEq : pendingKeys (events ++ [event])
      = pendingKeys events ++ newKeys := by
    simp [pendingKeys, List.flatMap_append, pending]
  have completedEq : completedKeys (events ++ [event])
      = completedKeys events := by
    simp [completedKeys, List.flatMap_append, noCompletion]
  simp only [Open, announcedKeys, pendingEq, completedEq,
    List.mem_append]
  constructor
  · rintro ⟨announced, notCompleted⟩
    rcases announced with initialMember | oldOrNew
    · exact Or.inl ⟨Or.inl initialMember, notCompleted⟩
    · rcases oldOrNew with oldMember | newMember
      · exact Or.inl ⟨Or.inr oldMember, notCompleted⟩
      · exact Or.inr newMember
  · rintro (⟨announced, notCompleted⟩ | newMember)
    · rcases announced with initialMember | oldMember
      · exact ⟨Or.inl initialMember, notCompleted⟩
      · exact ⟨Or.inr (Or.inl oldMember), notCompleted⟩
    · exact ⟨Or.inr (Or.inr newMember), fresh key newMember⟩

/-- A stream-value batch adds exactly the freshly announced group and stream
nodes to the publisher registry. -/
theorem IncrementalPublisher.registry_streamValues
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (stream : Execution.DeliveryNode)
    (values : List StreamItemValue)
    (groups streams : List Execution.DeliveryNode)
    (registry : publisher.RegistryMatchesOpen initial events)
    (fresh
      : ∀ key ∈ (groups ++ streams).map Execution.DeliveryNode.key,
          key ∉ completedKeys events)
    : ((publisher.handleWorkQueueEvent
          (.streamValues stream values groups streams)).1).RegistryMatchesOpen
        initial
        (events
          ++ (publisher.handleWorkQueueEvent
                (.streamValues stream values groups streams)).2) := by
  intro key
  change key ∈ (publisher.active ++ groups ++ streams).map
      Execution.DeliveryNode.key
    ↔ Open initial
        (events ++ [Execution.WorkQueueEvent.streamValues stream
          values
          groups streams]) key
  simp only [List.map_append, List.mem_append]
  rw [registry]
  have bridge := open_append_announcement initial events
    (.streamValues stream
      values
      groups streams)
    ((groups ++ streams).map Execution.DeliveryNode.key) key rfl rfl fresh
  simpa only [List.map_append, List.mem_append, or_assoc] using bridge.symm

/-- Outputs without notices or completions do not change abstract openness. -/
private theorem IncrementalPublisher.registry_append_silent
    (publisher : IncrementalPublisher) (initial : Keys)
    (events added : List Execution.WorkQueueEvent)
    (registry : publisher.RegistryMatchesOpen initial events)
    (noPending : pendingKeys added = [])
    (noCompletion : completedKeys added = [])
    : publisher.RegistryMatchesOpen initial (events ++ added) := by
  intro key
  have pendingEq : pendingKeys (events ++ added) = pendingKeys events := by
    simp only [pendingKeys, List.flatMap_append]
    rw [show added.flatMap eventPending = [] from noPending]
    simp
  have completedEq : completedKeys (events ++ added) = completedKeys events := by
    simp only [completedKeys, List.flatMap_append]
    rw [show added.flatMap eventCompleted = [] from noCompletion]
    simp
  have openEq : Open initial (events ++ added) key = Open initial events key := by
    simp only [Open, announcedKeys, pendingEq, completedEq]
  simpa only [openEq] using registry key

/-- Shared-value publications leave the active/open registry unchanged. -/
theorem IncrementalPublisher.registry_groupValues
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (group : Execution.DeliveryNode) (values : List ExecutionGroupValue)
    (registry : publisher.RegistryMatchesOpen initial events)
    : ((publisher.handleWorkQueueEvent (.groupValues group values)).1).RegistryMatchesOpen
        initial
        (events ++ (publisher.handleWorkQueueEvent (.groupValues group values)).2) := by
  change publisher.RegistryMatchesOpen initial
    (events ++ values.map
      (fun value => Execution.WorkQueueEvent.groupValues
        (publisher.getBestIdAndSubPath group value)
        [value]))
  apply publisher.registry_append_silent initial events _ registry
  · simp [pendingKeys, List.flatMap_map, eventPending]
  · simp [completedKeys, List.flatMap_map, eventCompleted]

/-- The terminal marker changes neither active nodes nor abstract openness. -/
theorem IncrementalPublisher.registry_termination
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (registry : publisher.RegistryMatchesOpen initial events)
    : ((publisher.handleWorkQueueEvent .workQueueTermination).1).RegistryMatchesOpen
        initial (events ++ (publisher.handleWorkQueueEvent .workQueueTermination).2) := by
  change publisher.RegistryMatchesOpen initial
    (events ++ [Execution.WorkQueueEvent.workQueueTermination])
  apply publisher.registry_append_silent initial events _ registry
  · rfl
  · rfl

/-- The local freshness condition needed when one raw queue event creates new
publisher notices. It constrains only `GROUP_SUCCESS` and `STREAM_VALUES`.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.FreshNotices
    (events : List Execution.WorkQueueEvent)
    : WorkQueueEvent → Prop
  | .groupSuccess group groups streams =>
      ∀ key ∈ (groups ++ streams).map Execution.DeliveryNode.key,
        key ∉ completedKeys events ∧ key ≠ group.key
  | .streamValues _ _ groups streams =>
      ∀ key ∈ (groups ++ streams).map Execution.DeliveryNode.key,
        key ∉ completedKeys events
  | _ => True

/-- Every raw publisher transition preserves active/open agreement when its
new notices are fresh. Witnesses are the six event-specific registry lemmas.
-/
theorem IncrementalPublisher.RegistryMatchesOpen.handleWorkQueueEvent
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (raw : WorkQueueEvent)
    (registry : publisher.RegistryMatchesOpen initial events)
    (fresh : WorkQueueEvent.FreshNotices events raw)
    : ((publisher.handleWorkQueueEvent raw).1).RegistryMatchesOpen
        initial (events ++ (publisher.handleWorkQueueEvent raw).2) := by
  cases raw with
  | groupValues group values =>
      exact publisher.registry_groupValues initial events group values registry
  | groupSuccess group groups streams =>
      exact publisher.registry_groupSuccess initial events group groups streams
        registry fresh
  | groupFailure group errors =>
      exact publisher.registry_groupFailure initial events group errors registry
  | streamValues stream values groups streams =>
      exact publisher.registry_streamValues initial events stream values groups streams
        registry fresh
  | streamSuccess stream =>
      exact publisher.registry_streamSuccess initial events stream registry
  | streamFailure stream errors =>
      exact publisher.registry_streamFailure initial events stream errors registry
  | workQueueTermination =>
      exact publisher.registry_termination initial events registry

/-- Freshness across a raw batch is checked at each successive publisher state
and normalized output prefix, since earlier events in the same batch may close
or announce keys.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.FreshBatch
    (publisher : IncrementalPublisher) (events : List Execution.WorkQueueEvent)
    : List WorkQueueEvent → Prop
  | [] => True
  | raw :: rest =>
      WorkQueueEvent.FreshNotices events raw
      ∧ FreshBatch
          (publisher.handleWorkQueueEvent raw).1
          (events ++ (publisher.handleWorkQueueEvent raw).2) rest

/-- The executable batch fold preserves active/open agreement at every fresh
raw event, including multiple announcements and closures in one batch.
-/
theorem IncrementalPublisher.RegistryMatchesOpen.normalizeBatch
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent)
    (raw : List WorkQueueEvent)
    (registry : publisher.RegistryMatchesOpen initial events)
    (fresh : WorkQueueEvent.FreshBatch publisher events raw)
    : ((publisher.normalizeBatch raw).1).RegistryMatchesOpen
        initial (events ++ (publisher.normalizeBatch raw).2) := by
  let step (acc : IncrementalPublisher × List Execution.WorkQueueEvent)
      (event : WorkQueueEvent) : IncrementalPublisher × List Execution.WorkQueueEvent :=
    let (current, output) := acc
    let (next, produced) := current.handleWorkQueueEvent event
    (next, output ++ produced)
  have loop (remaining : List WorkQueueEvent) :
      ∀ current output,
        current.RegistryMatchesOpen initial (events ++ output)
        → WorkQueueEvent.FreshBatch current (events ++ output) remaining
        → ((remaining.foldl step (current, output)).1).RegistryMatchesOpen
            initial (events ++ (remaining.foldl step (current, output)).2) := by
    induction remaining with
    | nil =>
        intro current output currentRegistry _
        exact currentRegistry
    | cons raw rest ih =>
        intro current output currentRegistry freshBatch
        obtain ⟨freshHead, freshTail⟩ := freshBatch
        let next := (current.handleWorkQueueEvent raw).1
        let produced := (current.handleWorkQueueEvent raw).2
        have nextRegistry : next.RegistryMatchesOpen initial
            (events ++ (output ++ produced)) := by
          simpa only [List.append_assoc]
            using IncrementalPublisher.RegistryMatchesOpen.handleWorkQueueEvent
              current initial (events ++ output) raw currentRegistry freshHead
        have tailFresh : WorkQueueEvent.FreshBatch next
            (events ++ (output ++ produced)) rest := by
          simpa only [List.append_assoc] using freshTail
        change ((rest.foldl step (next, output ++ produced)).1).RegistryMatchesOpen
          initial (events ++ (rest.foldl step (next, output ++ produced)).2)
        exact ih next (output ++ produced) nextRegistry tailFresh
  change ((raw.foldl step (publisher, [])).1).RegistryMatchesOpen
    initial (events ++ (raw.foldl step (publisher, [])).2)
  exact loop raw publisher [] (by simpa using registry) (by simpa using fresh)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
