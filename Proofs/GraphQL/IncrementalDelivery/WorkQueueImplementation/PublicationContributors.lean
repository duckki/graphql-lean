import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValues
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipSoundness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawPublicationClosures

/-! Raw release groups really contribute to every stored value they publish. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Reuse registered-task, membership, and stored-value provenance together
-----------------------------------------------------------------------------------------

/-- Local proof evidence connecting live group memberships to stored contributor lists.
It packages existing state predicates, not a new source law or implementation field.
-/
structure State.ContributorProvenance (queue : State) (work : Execution.Work) : Prop where
  registered : queue.RegisteredTasksMatch work
  memberships : queue.GroupMembershipSound
  stored
    : queue.StoredValuesSatisfy
        (fun occurrence value => taskGroups? work occurrence = some value.deliveryGroups)

/-- Raw object values name their releasing group among their contributing refs.
This says nothing about the publisher's subsequently selected wire owner.
-/
def RawPublicationContributors (events : List WorkQueueEvent) : Prop :=
  ∀ group values,
    .groupValues group values ∈ events
    → ∀ value ∈ values, group.ref ∈ value.deliveryGroups.map Execution.DeliveryNode.ref

/-- Concatenated output blocks retain each publication's own contributing release group.
Witness: select the block containing the raw event.
-/
theorem RawPublicationContributors.append {left right}
    (first : RawPublicationContributors left) (later : RawPublicationContributors right)
    : RawPublicationContributors (left ++ right) := by
  intro group values emitted value member
  rcases List.mem_append.mp emitted with before | after
  · exact first group values before value member
  · exact later group values after value member

/-- A successful flush can emit only values contributed by that live group.
Witness: exact flush selection, sound group memberships, and the common structural
contributor list of the registered task and its stored successful value.
-/
theorem State.ContributorProvenance.finishGroupSuccess_outputs {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (group : GroupNode) (present : group ∈ queue.groupNodes)
    : RawPublicationContributors (queue.finishGroupSuccess group).2.1 := by
  intro trigger values emitted value member
  obtain ⟨same, node, storedNode, inGroup, storedValue, _⟩ :=
    State.finishGroupSuccess_value emitted member
  obtain ⟨task, registered, occurrenceEq, contributes⟩ :=
    provenance.memberships group present node.task.occurrence inGroup
  have groups := (provenance.registered task registered).2
  rw [occurrenceEq] at groups
  have exactGroups := provenance.stored node storedNode value storedValue
  have sameGroups : task.groups = value.deliveryGroups := Option.some.inj
    (groups.symm.trans exactGroups)
  simpa only [same, ← sameGroups] using contributes

/-- Changing only a live group's counter preserves contributor provenance.
Witness: its registered tasks and stored values are unchanged, and memberships are copied.
-/
theorem State.ContributorProvenance.decrement {queue : State} {work : Execution.Work}
    (provenance : queue.ContributorProvenance work) {group : GroupNode}
    (present : group ∈ queue.groupNodes)
    : (queue.putGroupNode
        { group with pending := group.pending - 1 }).ContributorProvenance
        work :=
  ⟨
    provenance.registered.putGroupNode _,
    provenance.memberships.putGroupNode _ (provenance.memberships group present),
    provenance.stored.putGroupNode _
  ⟩

/-- Successful flushing preserves the provenance of all remaining stored memberships.
Witness: reuse the three existing independent preservation proofs.
-/
theorem State.ContributorProvenance.finishGroupSuccess {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ContributorProvenance work :=
  ⟨
    provenance.registered.finishGroupSuccess group,
    provenance.memberships.finishGroupSuccess group,
    provenance.stored.finishGroupSuccess group
  ⟩

/-- Failed closure removes live records without altering remaining contributor metadata.
Witness: registered-task, membership, and stored-value preservation under group removal.
-/
theorem State.ContributorProvenance.finishGroupFailure {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (group : GroupNode) (errors : Nat)
    : (queue.finishGroupFailure group errors).1.ContributorProvenance work :=
  ⟨
    provenance.registered.finishGroupFailure group errors,
    provenance.memberships.finishGroupFailure group errors,
    provenance.stored.removeGroup group.group.node.ref
  ⟩

/-- Activating newly announced work preserves all contributor provenance.
Witness: starting tasks never installs successful values or changes task ownership.
-/
theorem State.ContributorProvenance.startNewWork {queue : State} {work : Execution.Work}
    (provenance : queue.ContributorProvenance work) (newWork : NewWork)
    : (queue.startNewWork newWork).ContributorProvenance work :=
  ⟨
    provenance.registered.startNewWork newWork,
    provenance.memberships.startNewWork newWork,
    provenance.stored.startNewWork newWork
  ⟩

/-- Integrating located child tasks preserves registered and stored contributor agreement.
Witness: registration adds sound memberships; no child result is installed at integration.
-/
theorem State.ContributorProvenance.maybeIntegrateWork {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (children : Work) (located : ∀ task ∈ children.tasks, TaskMatches work task)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork children producer).1.ContributorProvenance work :=
  ⟨
    provenance.registered.maybeIntegrateWork children located producer,
    provenance.memberships.maybeIntegrateWork children producer,
    provenance.stored.maybeIntegrateWork children producer
  ⟩

/-- Empty-group pruning preserves contributor provenance on surviving records.
Witness: pruning neither invents tasks nor installs successful values.
-/
theorem State.ContributorProvenance.pruneEmptyGroups {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ContributorProvenance work :=
  ⟨
    provenance.registered.pruneEmptyGroups groups,
    provenance.memberships.pruneEmptyGroups groups,
    provenance.stored.pruneEmptyGroups groups
  ⟩

-----------------------------------------------------------------------------------------
-- Follow every actual release path, including recursive and stream-triggered drains
-----------------------------------------------------------------------------------------

/-- Every drained object is released by a contributing live group.
Witness: each successful branch selects a present node and preserves the three provenance
facts through flushing and activation; failed branches emit no object value.
-/
theorem State.ContributorProvenance.drainReadyGroups_outputs {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    : RawPublicationContributors queue.drainReadyGroups.2 := by
  have loop (fuel : Nat) (current : State) (known : current.ContributorProvenance work)
      : RawPublicationContributors (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current with
    | zero => intro _ _ impossible; cases impossible
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · intro _ _ impossible; cases impossible
        · rename_i group found
          have present : group ∈ current.groupNodes := by
            obtain ⟨ref, _, choice⟩ := List.exists_of_findSome?_eq_some found
            cases lookup : current.groupNode? ref with
            | none => simp [lookup] at choice
            | some candidate =>
                simp only [lookup] at choice
                change (if _ then some candidate else none) = some group at choice
                split at choice
                · cases Option.some.inj choice
                  exact List.mem_of_find?_eq_some lookup
                · contradiction
          cases cached : group.failure with
          | none =>
              exact (known.finishGroupSuccess_outputs group present).append
                (ih _ ((known.finishGroupSuccess group).startNewWork _))
          | some errors =>
              apply RawPublicationContributors.append
              · intro _ _ impossible
                simp [State.finishGroupFailure] at impossible
              · exact ih _ (known.finishGroupFailure group errors)
  exact loop _ queue provenance

/-- A successful settlement preserves release-group contribution through every owner
fold and its final drain. Witness: install the source's exact contributor list, then
use live membership soundness at each actual flush, including the decremented node.
-/
theorem State.ContributorProvenance.taskSuccess_outputs {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (occurrence : Occurrence) (result : TaskResult)
    (groups : taskGroups? work occurrence = some result.value.deliveryGroups)
    (children : ∀ task ∈ result.work.tasks, TaskMatches work task)
    : RawPublicationContributors (queue.taskSuccess occurrence result).2 := by
  have loop (owners : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (known : acc.1.ContributorProvenance work) (outputs : RawPublicationContributors acc.2.1)
      : (owners.foldl successGroupStep acc).1.ContributorProvenance work
        ∧ RawPublicationContributors (owners.foldl successGroupStep acc).2.1 := by
    induction owners generalizing acc with
    | nil => exact ⟨known, outputs⟩
    | cons owner rest ih =>
        apply ih
        · dsimp only [successGroupStep]
          split
          · exact known
          · rename_i group found
            have decremented := known.decrement (List.mem_of_find?_eq_some found)
            split
            · exact decremented.finishGroupSuccess _
            · exact decremented
        · dsimp only [successGroupStep]
          split
          · exact outputs
          · rename_i group found
            have present := List.mem_of_find?_eq_some found
            have decremented := known.decrement present
            split
            · apply outputs.append (decremented.finishGroupSuccess_outputs _ ?_)
              apply List.mem_map.mpr
              refine ⟨group, present, ?_⟩
              simp
            · exact outputs
  cases found : queue.taskNode? occurrence with
  | none => intro _ _ impossible; simp [State.taskSuccess, found] at impossible
  | some node =>
      have installed : (queue.putTaskNode
          { node with value := some result.value }).ContributorProvenance work := by
        refine ⟨provenance.registered, provenance.memberships,
          provenance.stored.putTaskNode _ ?_⟩
        intro value same
        cases same
        simpa only [(State.taskNode?_some found).2] using groups
      have integrated := installed.maybeIntegrateWork result.work children (some occurrence)
      obtain ⟨retained, outputs⟩ := loop node.task.groups (_, [], {}) integrated
        (by intro _ _ impossible; cases impossible)
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · intro _ _ impossible; cases impossible
      · exact outputs.append (retained.startNewWork _).drainReadyGroups_outputs

/-- Stream arrivals can release earlier buffered objects without changing their owners.
Witness: child integration and pruning preserve provenance; only the final drain emits
object values, and its live release groups satisfy the same membership theorem.
-/
theorem State.ContributorProvenance.streamItems_outputs {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (children : ∀ item ∈ items, ∀ task ∈ item.work.tasks, TaskMatches work task)
    : RawPublicationContributors (queue.streamItems stream items).2 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (subset : ∀ item ∈ more, item ∈ items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (known : acc.1.ContributorProvenance work)
      : (more.foldl step acc).1.ContributorProvenance work := by
    induction more generalizing acc with
    | nil => exact known
    | cons item rest ih =>
        apply ih (fun candidate member => subset candidate (by simp [member]))
        exact ((known.maybeIntegrateWork item.work
                  (children item (subset item List.mem_cons_self))).pruneEmptyGroups
                _).startNewWork
          _
  have retained := loop items (fun _ member => member) (queue, [], [], []) provenance
  unfold State.streamItems
  split
  · intro _ _ impossible; cases impossible
  · intro trigger values emitted value member
    exact retained.drainReadyGroups_outputs trigger values
      ((List.mem_cons.mp emitted).resolve_left (by intro impossible; cases impossible))
      value member

-----------------------------------------------------------------------------------------
-- Valid source replay supplies the provenance without assuming output admission
-----------------------------------------------------------------------------------------

/-- Matched source events preserve all three local contributor facts.
Witness: existing handler preservation and exact successful-source group matching.
-/
theorem State.ContributorProvenance.handleGraphEvent {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.ContributorProvenance work := by
  refine ⟨provenance.registered.handleGraphEvent event matching,
    provenance.memberships.handleGraphEvent event,
    provenance.stored.handleGraphEvent event ?_⟩
  intro occurrence result same
  subst event
  obtain ⟨_, _, _, groups, _⟩ := matching
  exact groups

/-- Each matched source handler publishes values only through a genuine contributor.
Witness: success and stream drains use the provenance lemmas; the other constructors
cannot emit object publications.
-/
theorem State.ContributorProvenance.handleGraphEvent_outputs {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : RawPublicationContributors (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess occurrence result =>
      apply provenance.taskSuccess_outputs occurrence result
      · obtain ⟨_, _, _, groups, _⟩ := matching
        exact groups
      · intro task member
        obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
        exact ⟨⟨address, payload, some occurrence, same, known⟩,
          matching.childTask_groupsExact member⟩
  | taskFailure occurrence errors =>
      intro group values emitted value member
      obtain ⟨_, impossible⟩ := queue.taskFailure_publishedValues occurrence errors
        (fun _ _ => False) group values emitted value member
      exact False.elim impossible
  | streamItems stream items =>
      apply provenance.streamItems_outputs stream items
      intro item itemMember task taskMember
      obtain ⟨address, payload, same, known⟩ :=
        matching.streamItem_childTask_producer itemMember taskMember
      exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
        matching.streamItem_childTask_groupsExact itemMember taskMember⟩
  | streamSuccess stream =>
      intro group values emitted
      simp only [State.handleGraphEvent, State.streamSuccess] at emitted
      split at emitted <;> simp at emitted
  | streamFailure stream errors =>
      intro group values emitted
      simp only [State.handleGraphEvent, State.streamFailure] at emitted
      split at emitted <;> simp at emitted

/-- Complete raw replay preserves contributor membership at every actual publication.
Witness: source-list induction threads the three proven state facts through each handler.
-/
theorem State.ContributorProvenance.rawEventReplay_outputs {queue : State}
    {work : Execution.Work} (provenance : queue.ContributorProvenance work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : RawPublicationContributors (queue.rawEventReplay events).2 := by
  induction events generalizing queue with
  | nil => intro _ _ impossible; cases impossible
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      have head := matching event List.mem_cons_self
      exact (provenance.handleGraphEvent_outputs event head).append
        (ih (provenance.handleGraphEvent event head)
          (fun candidate member => matching candidate (by simp [member])))

/-- Every raw object publication from valid source replay uses a contributing group.
Witness: initial structural task/membership provenance and vacuous stored-value agreement,
followed by the actual handler replay. No scheduler admission or generated-work restriction
is needed for this metadata fact.
-/
theorem createWorkQueue_rawEventReplay_publicationContributors {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    : RawPublicationContributors
        ((State.initialize (Work.fromExecution work)).rawEventReplay events).2 := by
  have initial : (State.initialize (Work.fromExecution work)).ContributorProvenance work :=
    ⟨createWorkQueue_fromSpec_registeredTasksMatch work,
      createWorkQueue_groupMembershipSound _, createWorkQueue_storedValues _ _⟩
  exact initial.rawEventReplay_outputs events (fun _ member => valid.event_matches member)

/-- Each raw value still has its exact successful source event, including contributors.
Witness: the unchanged raw publication ledger retains the full value, not just its
serialized data. This avoids inferring ownership from possibly equal response payloads.
-/
theorem createWorkQueue_rawEventReplay_valueSource {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    {group values value}
    (emitted
      : .groupValues group values
        ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay events).2)
    (member : value ∈ values)
    : ∃ occurrence result,
        GraphEvent.taskSuccess occurrence result ∈ events
        ∧ result.value = value
        ∧ (GraphEvent.taskSuccess occurrence result).MatchesWork work := by
  obtain ⟨published, exactValues, inventory⟩ := createWorkQueue_rawEventReplay_publications valid
  have inValues : value ∈ published.map Prod.snd := by
    rw [exactValues]
    exact List.mem_flatMap.mpr ⟨_, emitted, member⟩
  obtain ⟨publication, selected, same⟩ := List.mem_map.mp inValues
  obtain ⟨result, supplied, stored⟩ := inventory.provenance publication selected
  exact ⟨publication.1, result, supplied, stored.trans same, valid.event_matches supplied⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
