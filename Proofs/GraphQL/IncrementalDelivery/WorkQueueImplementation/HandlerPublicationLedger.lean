import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskHandlerPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamHandlerPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Source handlers retain one ledger for buffered closures and stream release.
Prepared-state predicates take the queue after cache exposure, matching host dispatch. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- One event-level certificate preserves the prepared-state evidence where it is needed
-----------------------------------------------------------------------------------------

/-- A successful input's prepared task map is covered at its handler's output carriers.
`published` labels that handler's object values. Other input kinds install no successful
object value and impose no prepared-state clause; their old values use buffered coverage.
-/
def State.PreparedClosuresCovered (queue : State) (event : GraphEvent)
    (published : List ObjectPublication) (available : List (Occurrence × Nat) := [])
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → let stored := queue.putTaskNode { node with value := some result.value }
          let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
          prepared.BufferedClosuresCovered published
            (queue.taskSuccess occurrence result available).2.1
  | _ => True

/-- A successful input's prepared values are conserved through its remaining handler.
`published` labels that handler's object values. Other inputs have no prepared object map.
-/
def State.PreparedValuesConserved (queue : State) (event : GraphEvent)
    (published : List ObjectPublication) (available : List (Occurrence × Nat) := [])
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.StoredValuesConserved
            published (queue.taskSuccess occurrence result available).1
  | _ => True

/-- A successful input retains its prepared buffered owners until publication or cancellation.
`published` is the same handler ledger used for values and closure coverage. Other source
events install no object value and therefore impose no prepared-state owner obligation.
-/
def State.PreparedOwnersConserved (queue : State) (event : GraphEvent)
    (published : List ObjectPublication) (available : List (Occurrence × Nat) := [])
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.StoredOwnersConserved
            published (queue.taskSuccess occurrence result available).1
  | _ => True

/-- A value-producing input conserves buffered owners throughout owner processing and drain.
`published` fixes the whole handler's labels, including values flushed by the preceding
task-owner fold. Item handlers retain their entry buffers through preparation and each
drain prefix. Failure and stream-closure inputs do not emit object values.
-/
def State.PreparedReleaseOwners (queue : State) (event : GraphEvent)
    (published : List ObjectPublication) (available : List (Occurrence × Nat) := [])
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.ReleaseOwners
            node.task.groups published available
  | .streamItems stream items => queue.StreamDrainOwners stream items published available
  | _ => True

/-- A value-producing handler excludes earlier emitted memberships at release boundaries.
`published` is the same handler slice used for producer coverage and owner conservation.
Other source events emit no object values and have no successful release-drain phase.
-/
def State.PreparedMembershipsCleared (queue : State) (event : GraphEvent)
    (published : List ObjectPublication) (available : List (Occurrence × Nat) := [])
    : Prop :=
  match event with
  | .taskSuccess occurrence result =>
      ∀ node,
        queue.taskNode? occurrence = some node
        → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.ReleaseMembershipsCleared
            node.task.groups published available
  | .streamItems stream items =>
      queue.StreamDrainMembershipsCleared stream items published available
  | _ => True

/-- Every fresh matching host event has one joint ledger after cache exposure.
Prepared-state evidence is indexed by that same cached input queue. Successful source
provenance excludes its buffered values from the supplied rejection snapshot.
-/
theorem State.PublicationInventory.handleGraphEvent_bufferedCoverage {queue : State}
    {work before published settledTasks}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work settledTasks)
    (included : settledTasks.Subset (before.flatMap (fun event => event.identities.1)))
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (event : GraphEvent)
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (memberships : queue.GroupMembershipOrder) (cancelled : queue.CancellationsRetired)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          ObjectValueFrom (before ++ [event]) occurrence value
          → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value allowed errors impossible; cases impossible)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvent event available).2.1.flatMap
              WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvent event available).1.PublicationInventory
            (ObjectValueFrom (before ++ [event])) (published ++ added)
        ∧ queue.BufferedClosuresCovered added (queue.handleGraphEvent event available).2.1
        ∧ (queue.cacheTaskFailures available).PreparedClosuresCovered event added
            available
        ∧ StreamReleasePublications work added
            (queue.handleGraphEvent event available).2.1
        ∧ queue.StoredValuesConserved added (queue.handleGraphEvent event available).1
        ∧ (queue.cacheTaskFailures available).PreparedValuesConserved event added
            available
        ∧ BlocksFollowRegistrations (queue.handleGraphEvent event available).1.tasks added
            (queue.handleGraphEvent event available).2.1
        ∧ queue.StoredOwnersConserved added (queue.handleGraphEvent event available).1
        ∧ (queue.cacheTaskFailures available).PreparedOwnersConserved event added
            available
        ∧ (queue.cacheTaskFailures available).PreparedReleaseOwners event added available
        ∧ (queue.cacheTaskFailures available).PreparedMembershipsCleared event added
            available := by
  let cached := queue.cacheTaskFailures available
  have cachedInventory : cached.PublicationInventory (ObjectValueFrom before) published :=
    ⟨inventory.unique, inventory.provenance, inventory.stored.cacheTaskFailures available⟩
  have cachedAccounting := accounted.cacheTaskFailures available
  have cachedLinks := links.cacheTaskFailures available
  have cachedSettled := settled.cacheTaskFailures available
  have cachedChildren := children.cacheTaskFailures available
  have cachedMemberships := memberships.cacheTaskFailures available
  have cachedCancellations := cancelled.cacheTaskFailures available
  have current := inventory.mono (fun _ _ source =>
    source.mono (List.subset_append_left before [event]))
  have cachedCurrent := cachedInventory.mono (fun _ _ source =>
    source.mono (List.subset_append_left before [event]))
  have after : ∃ added : List ObjectPublication,
      added.map Prod.snd
        = (queue.handleGraphEvent event available).2.1.flatMap WorkQueueEvent.objectValues
      ∧ (queue.handleGraphEvent event available).1.PublicationInventory
          (ObjectValueFrom (before ++ [event])) (published ++ added)
      ∧ cached.BufferedClosuresCovered added (queue.handleGraphEvent event available).2.1
      ∧ cached.PreparedClosuresCovered event added available
      ∧ StreamReleasePublications work added (queue.handleGraphEvent event available).2.1
      ∧ cached.StoredValuesConserved added (queue.handleGraphEvent event available).1
      ∧ cached.PreparedValuesConserved event added available
      ∧ BlocksFollowRegistrations (queue.handleGraphEvent event available).1.tasks added
          (queue.handleGraphEvent event available).2.1
      ∧ cached.StoredOwnersConserved added (queue.handleGraphEvent event available).1
      ∧ cached.PreparedOwnersConserved event added available
      ∧ cached.PreparedReleaseOwners event added available
      ∧ cached.PreparedMembershipsCleared event added available := by
    cases event with
    | taskSuccess occurrence result =>
        exact cachedInventory.taskSuccess_bufferedCoverage generated cachedAccounting included
          cachedLinks cachedSettled cachedChildren occurrence result matching fresh
          cachedMemberships
          available clean
    | streamItems stream items =>
        obtain ⟨added, values, final, covered, streams, conserved,
          ordered, owners, prefixes, cleared⟩ := cachedCurrent.streamItems_bufferedCoverage
            generated cachedAccounting.refs cachedAccounting.liveGroups cachedAccounting.taskGroups
            cachedAccounting.started cachedLinks cachedSettled cachedChildren stream items
            (fun _ member => matching.streamItem_childTasksCovered generated.declarations member) cachedMemberships
            cachedCancellations available clean
        exact ⟨added, values, final, covered, trivial, streams, conserved, trivial, ordered,
          owners, trivial, prefixes, cleared⟩
    | taskFailure occurrence errors =>
        obtain ⟨added, values, final, streams⟩ := current.handleGraphEvent_streamRelease
          settled children generated (.taskFailure occurrence errors) matching
          (by intro task result impossible; cases impossible) available
        refine ⟨
          added,
          values,
          final,
          .of_noGroupSuccess (cached.taskFailure_noGroupSuccess occurrence errors),
          trivial,
          streams,
          ?_,
          trivial,
          BlocksFollowRegistrations.of_noObjectValues _ _
            (cached.taskFailure_objectValues occurrence errors),
          (cachedInventory.taskFailure_storedOwnersConserved occurrence errors
            fresh).of_empty
            added,
          trivial,
          trivial,
          trivial
        ⟩
        intro task node value found stored survivor
        have known := State.taskNode?_some found
        have source := (cachedInventory.stored node known.1 value stored).1
        have different : task ≠ occurrence := by
          intro same
          exact fresh.2.2.1 occurrence List.mem_cons_self
            (same ▸ known.2 ▸ source.identity)
        obtain ⟨contributor, contributes, owner, live⟩ := survivor
        exact Or.inr
          (State.taskFailure_lookup_survivingOwner found occurrence errors different
            contributes (List.mem_of_find?_eq_some live) (State.groupNode?_ref live))
    | streamSuccess stream =>
        obtain ⟨added, values, final, streams⟩ := current.handleGraphEvent_streamRelease
          settled children generated (.streamSuccess stream) matching
          (by intro task result impossible; cases impossible) available
        have owners : cached.StoredOwnersConserved added (cached.streamSuccess stream).1 := by
          intro occurrence node value found stored ref contributes present uncancelled
          unfold State.streamSuccess
          split <;> exact Or.inr ⟨found, present⟩
        refine ⟨
          added,
          values,
          final,
          .of_noGroupSuccess ?_,
          trivial,
          streams,
          ?_,
          trivial,
          BlocksFollowRegistrations.of_noObjectValues _ _ ?_,
          owners,
          trivial,
          trivial,
          trivial
        ⟩
        · intro group groups streams
          simp only [State.handleGraphEvent, State.streamSuccess]
          split <;> simp
        · intro task node value found _ _
          apply Or.inr
          change (cached.streamSuccess stream).1.taskNode? task = some node
          unfold State.streamSuccess
          split <;> exact found
        · simp only [State.handleGraphEvent, State.streamSuccess]
          split <;> rfl
    | streamFailure stream errors =>
        obtain ⟨added, values, final, streams⟩ := current.handleGraphEvent_streamRelease
          settled children generated (.streamFailure stream errors) matching
          (by intro task result impossible; cases impossible) available
        have owners : cached.StoredOwnersConserved added (cached.streamFailure stream errors).1
          := by
          intro occurrence node value found stored ref contributes present uncancelled
          unfold State.streamFailure
          split <;> exact Or.inr ⟨found, present⟩
        refine ⟨
          added,
          values,
          final,
          .of_noGroupSuccess ?_,
          trivial,
          streams,
          ?_,
          trivial,
          BlocksFollowRegistrations.of_noObjectValues _ _ ?_,
          owners,
          trivial,
          trivial,
          trivial
        ⟩
        · intro group groups streams
          simp only [State.handleGraphEvent, State.streamFailure]
          split <;> simp
        · intro task node value found _ _
          apply Or.inr
          change (cached.streamFailure stream errors).1.taskNode? task = some node
          unfold State.streamFailure
          split <;> exact found
        · simp only [State.handleGraphEvent, State.streamFailure]
          split <;> rfl
    | groupFailure notice =>
        obtain ⟨added, values, final, streams⟩ := current.handleGraphEvent_streamRelease
          settled children generated (.groupFailure notice) matching
          (by intro task result impossible; cases impossible) available
        have owners : cached.StoredOwnersConserved added (cached.groupFailure notice).1
          := by
          intro occurrence node value found stored ref contributes present uncancelled
          unfold State.groupFailure
          split
          · exact Or.inr ⟨found, present⟩
          · split <;> exact Or.inr ⟨found, present⟩
        refine ⟨
          added,
          values,
          final,
          .of_noGroupSuccess ?_,
          trivial,
          streams,
          ?_,
          trivial,
          BlocksFollowRegistrations.of_noObjectValues _ _ ?_,
          owners,
          trivial,
          trivial,
          trivial
        ⟩
        · intro group groups streams
          simp only [State.handleGraphEvent, State.groupFailure]
          split
          · simp
          · split <;> simp
        · intro task node value found _ _
          apply Or.inr
          change (cached.groupFailure notice).1.taskNode? task = some node
          unfold State.groupFailure
          split
          · exact found
          · split <;> exact found
        · simp only [State.handleGraphEvent, State.groupFailure]
          split
          · rfl
          · split <;> rfl
  obtain ⟨added, values, final, covered, prepared, streams, conserved, preparedValues,
    ordered, owners, preparedOwners, releaseOwners, cleared⟩ := after
  have retained : ∀ occurrence node value,
      queue.taskNode? occurrence = some node → node.value = some value
      → cached.taskNode? occurrence = some node := by
    intro occurrence node value found stored
    have known := State.taskNode?_some found
    have source := (inventory.stored node known.1 value stored).1
    have safe := clean _ _ (source.mono (List.subset_append_left before [event]))
    exact State.cacheTaskFailures_lookup_existing found available (known.2 ▸ safe)
  refine ⟨added, values, final, covered.of_lookups retained, prepared, streams,
    conserved.of_lookups retained, preparedValues, ordered, owners.of_lookups retained ?_,
    preparedOwners, releaseOwners, cleared⟩
  intro ref member
  rwa [State.cacheTaskFailures_groupNodes]

/-- Enqueue effects preserve the exact handler ledger and its closure certificates. -/
theorem State.PublicationInventory.dispatchGraphEvent_bufferedCoverage {queue : State}
    {work before published settledTasks}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work settledTasks)
    (included : settledTasks.Subset (before.flatMap (fun event => event.identities.1)))
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (event : GraphEvent)
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (memberships : queue.GroupMembershipOrder) (cancelled : queue.CancellationsRetired)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          ObjectValueFrom (before ++ [event]) occurrence value
          → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value allowed errors impossible; cases impossible)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.dispatchGraphEvent event available).2.flatMap
              WorkQueueEvent.objectValues
        ∧ (queue.dispatchGraphEvent event available).1.PublicationInventory
            (ObjectValueFrom (before ++ [event])) (published ++ added)
        ∧ queue.BufferedClosuresCovered added (queue.dispatchGraphEvent event available).2
        ∧ (queue.cacheTaskFailures available).PreparedClosuresCovered event added
            available
        ∧ StreamReleasePublications work added
            (queue.dispatchGraphEvent event available).2
        ∧ queue.StoredValuesConserved added (queue.dispatchGraphEvent event available).1
        ∧ (queue.cacheTaskFailures available).PreparedValuesConserved event added
            available
        ∧ BlocksFollowRegistrations (queue.dispatchGraphEvent event available).1.tasks
            added (queue.dispatchGraphEvent event available).2
        ∧ queue.StoredOwnersConserved added (queue.dispatchGraphEvent event available).1
        ∧ (queue.cacheTaskFailures available).PreparedOwnersConserved event added
            available
        ∧ (queue.cacheTaskFailures available).PreparedReleaseOwners event added available
        ∧ (queue.cacheTaskFailures available).PreparedMembershipsCleared event added
            available := by
  obtain ⟨added, values, next, buffered, prepared, streams, conserved, installed,
    ordered, owners, preparedOwners, releaseOwners, cleared⟩ :=
    inventory.handleGraphEvent_bufferedCoverage generated accounted included links settled children
      event matching fresh memberships cancelled available clean
  exact ⟨added, values, ⟨next.unique, next.provenance, next.stored⟩, buffered, prepared,
    streams, conserved, installed, ordered, owners, preparedOwners, releaseOwners, cleared⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
