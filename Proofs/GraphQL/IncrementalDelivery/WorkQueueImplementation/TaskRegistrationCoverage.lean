import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegionRegistration

/-! Structural tasks are registered at their exact root or producer-integration boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Invert immediate lowering without traversing future producer boundaries
-----------------------------------------------------------------------------------------

/-- The existing lowering supplied at a structural task's registration boundary.
`none` selects initialization; an object or item producer selects its immediate child work.
This proof notation stores no future work or additional implementation state.
-/
def taskRegistrationWork? (work : Execution.Work) : Option Occurrence → Option Work
  | none => some (Work.fromExecution work)
  | some (.executionGroup address) => taskChildWork? work (.executionGroup address)
  | some (.item address index) => streamItemWork? work (.item address index)

/-- Every located subtree's immediate tasks belong to its producer's registration chunk.
Witness: combine edges preserve the current chunk; object/item edges select precisely the
existing child-work lookup. No execution-generated metadata or source law is required.
-/
theorem Located.taskRegistrationWork {root address current producer enclosing}
    (located : Located root address current producer enclosing)
    : ∃ chunk,
        taskRegistrationWork? root producer = some chunk
        ∧ (Work.fromExecution current address).tasks.Subset chunk.tasks := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact ⟨_, rfl, List.Subset.refl _⟩
  | left _ ih =>
      obtain ⟨chunk, same, included⟩ := ih
      exact ⟨chunk, same, (List.subset_append_left _ _).trans included⟩
  | right _ ih =>
      obtain ⟨chunk, same, included⟩ := ih
      exact ⟨chunk, same, (List.subset_append_right _ _).trans included⟩
  | executionGroup prior _ =>
      refine ⟨_, ?_, List.Subset.refl _⟩
      have found := prior.toCurrent
      unfold WorkQueueSemantics.Located at found
      simp [taskRegistrationWork?, taskChildWork?, found]
  | item prior entry _ =>
      refine ⟨_, ?_, List.Subset.refl _⟩
      have found := prior.toCurrent
      unfold WorkQueueSemantics.Located at found
      simp [taskRegistrationWork?, streamItemWork?, found, entry]

/-- An object task occurs in the chunk installed at its own producer boundary.
Witness: inverse immediate lowering retains its exact occurrence and contributor list.
The chunk contains all siblings at that boundary, but no tasks behind a later producer.
-/
theorem TaskAt.executionGroup_registrationWork
    {work address owners producer payload}
    (known : TaskAt work (.executionGroup address) owners producer payload)
    : ∃ chunk task,
        taskRegistrationWork? work producer = some chunk
        ∧ task ∈ chunk.tasks
        ∧ task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners
        ∧ taskGroups? work task.occurrence = some task.groups := by
  obtain ⟨groups, path, result, children, enclosing, located, sameOwners, _⟩ := known
  obtain ⟨chunk, boundary, included⟩ := Located.taskRegistrationWork located
  let task : Task := ⟨.executionGroup address, groups.map Execution.DeferredFragment.node⟩
  have immediate : task ∈ (Work.fromExecution (.executionGroup groups path result children)
      address).tasks := List.mem_cons_self
  refine ⟨chunk, task, boundary, included immediate, rfl, ?_, ?_⟩
  · simpa only [task, List.map_map, Function.comp_def] using sameOwners.symm
  · exact workFromSpec_tasks_groupsExact located immediate

/-- Every producer-free object task is present in the actual initial task registry.
Witness: its registration chunk is root lowering, and queue initialization keeps exactly
those task descriptors. This includes shared owners and taskless ancestor records.
-/
theorem TaskAt.executionGroup_initial_registered {work address owners payload}
    (known : TaskAt work (.executionGroup address) owners none payload)
    : ∃ task ∈ (State.initialize (Work.fromExecution work)).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨chunk, task, boundary, member, occurrence, groups, _⟩ :=
    TaskAt.executionGroup_registrationWork known
  have same : chunk = Work.fromExecution work := (Option.some.inj boundary).symm
  rw [same] at member
  exact ⟨task, (createWorkQueue_tasks _).symm ▸ member, occurrence, groups⟩

-----------------------------------------------------------------------------------------
-- Exact source child-work matching supplies the converse registration facts
-----------------------------------------------------------------------------------------

/-- A matched successful object producer supplies every immediate structural child task.
Witness: the source's exact child-work equation identifies the inverse-lowering chunk.
This proves supplied-work coverage, not that an ignored settlement integrates that work.
-/
theorem GraphEvent.MatchesWork.taskChildren_complete {work producer result}
    (matching : (GraphEvent.taskSuccess producer result).MatchesWork work)
    {address owners payload}
    (known : TaskAt work (.executionGroup address) owners (some producer) payload)
    : ∃ task ∈ result.work.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨chunk, task, boundary, member, occurrence, groups, _⟩ :=
    TaskAt.executionGroup_registrationWork known
  obtain ⟨_, _, _, _, childWork⟩ := matching
  cases producer with
  | item source index => cases childWork
  | executionGroup source =>
      have same : chunk = result.work := Option.some.inj (boundary.symm.trans childWork)
      exact ⟨task, same ▸ member, occurrence, groups⟩

/-- A matched stream item supplies every immediate structural child task.
Witness: item matching identifies exactly the chunk at that ordinal, not the next item
or all future children of the stream. No host timing or output admission is assumed.
-/
theorem GraphEvent.MatchesWork.streamItemChildren_complete {work stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (selected : item ∈ items) {address owners payload}
    (known : TaskAt work (.executionGroup address) owners (some item.occurrence) payload)
    : ∃ task ∈ item.work.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨chunk, task, boundary, member, occurrence, groups, _⟩ :=
    TaskAt.executionGroup_registrationWork known
  obtain ⟨_, _, _, childWork⟩ := matching item selected
  cases sameOccurrence : item.occurrence with
  | executionGroup source => simp [streamItemWork?, sameOccurrence] at childWork
  | item source index =>
      rw [sameOccurrence] at boundary childWork
      have same : chunk = item.work := Option.some.inj (boundary.symm.trans childWork)
      exact ⟨task, same ▸ member, occurrence, groups⟩

/-- A healthy accepted object success registers all structural children at that boundary.
Witness: exact source completeness and the executable task-registry append equation.
The explicit guard is essential: a started but ignored success must not reveal its work.
-/
theorem State.taskSuccess_child_registered {queue : State}
    {work producer result node} (found : queue.taskNode? producer = some node)
    (eligible : queue.taskHasHealthyOwner node.task = true)
    (matching : (GraphEvent.taskSuccess producer result).MatchesWork work)
    {address owners payload}
    (known : TaskAt work (.executionGroup address) owners (some producer) payload)
    : ∃ task ∈ (queue.taskSuccess producer result).1.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨task, member, occurrence, groups⟩ := matching.taskChildren_complete known
  rw [State.taskSuccess_tasks found eligible]
  exact ⟨task, List.mem_append_right _ member, occurrence, groups⟩

/-- Integrating an observed item registers its entire immediate structural task chunk.
Witness: matched item completeness and the integration append equation, including pruning
and activation. The caller must still establish that the stream handler accepts the item.
-/
theorem State.integrateStreamItem_child_registered (queue : State) {work stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (selected : item ∈ items) {address owners payload}
    (known : TaskAt work (.executionGroup address) owners (some item.occurrence) payload)
    : ∃ task ∈ (queue.integrateStreamItem item).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨task, member, occurrence, groups⟩ := matching.streamItemChildren_complete selected known
  rw [State.integrateStreamItem_tasks]
  exact ⟨task, List.mem_append_right _ member, occurrence, groups⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
