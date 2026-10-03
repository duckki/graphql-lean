import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionIntegration

/-! Actual event handlers preserve global membership exclusion on their publication ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Single-pass success retains one ledger for values and shared membership removal
-----------------------------------------------------------------------------------------

/-- A contributor step removes newly published memberships and preserves earlier exclusions.
Witness: counter updates retain task lists; the actual flush extends the same ledger and
removes every selected occurrence from all contributors before the next step.
-/
theorem successGroupStep_publicationMemberships {property published}
    (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
    {added : List ObjectPublication}
    (values : added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues)
    (inventory : acc.1.PublicationInventory property (published ++ added))
    (absent
      : ∀ publication ∈ published ++ added, acc.1.TaskMembershipAbsent publication.1)
    : ∃ next : List ObjectPublication,
        next.map Prod.snd
          = (successGroupStep acc group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (successGroupStep acc group).1.PublicationInventory property (published ++ next)
        ∧ ∀ publication ∈ published ++ next,
            (successGroupStep acc group).1.TaskMembershipAbsent publication.1 := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨added, values, inventory, absent⟩
  · rename_i owner found
    have updated := inventory.putGroupNode { owner with pending := owner.pending - 1 }
    have excluded (publication) (member : publication ∈ published ++ added) :=
      (absent publication member).putGroupNode { owner with pending := owner.pending - 1 }
        (absent publication member owner (List.mem_of_find?_eq_some found))
    split
    · obtain ⟨extra, exactValues, nextInventory, nextAbsent⟩ :=
        updated.finishGroupSuccess_memberships excluded { owner with pending := owner.pending - 1 }
      refine ⟨added ++ extra, ?_, ?_, ?_⟩
      · simp only [List.map_append, List.flatMap_append, values, exactValues]
      · simpa only [List.append_assoc] using nextInventory
      · simpa only [List.append_assoc] using nextAbsent
    · exact ⟨added, values, updated, excluded⟩

/-- Task success excludes all delivered memberships, including shared-owner publications.
Witness: integrate only fresh child identities, then thread a joint publication/removal
ledger through the actual single-pass owner fold, activation, and recursive drain.
-/
theorem State.PublicationInventory.taskSuccess_memberships {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    (occurrence : Occurrence) (result : TaskResult)
    (allowed : property occurrence result.value)
    (fresh : occurrence ∉ published.map Prod.fst)
    (childrenFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ published.map Prod.fst)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.taskSuccess occurrence result).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.taskSuccess occurrence result).1.PublicationInventory property
            (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            (queue.taskSuccess occurrence result).1.TaskMembershipAbsent
              publication.1 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      exact ⟨[], rfl, by simpa using inventory, by simpa using absent⟩
  | some node =>
      have equal := (State.taskNode?_some found).2
      have installed := inventory.stored.putTaskNode { node with value := some result.value } (by
        intro value same
        cases same
        simpa only [equal] using And.intro allowed fresh)
      have integrated := installed.maybeIntegrateWork result.work (some occurrence)
      have integratedAbsent (publication) (member : publication ∈ published)
          : ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
              result.work (some occurrence)).1.TaskMembershipAbsent publication.1 := by
        apply ((absent publication member).putTaskNode
          { node with value := some result.value }).maybeIntegrateWork result.work
            (parentTask := some occurrence)
        intro child childMember same
        exact childrenFresh child childMember
          (List.mem_map.mpr ⟨publication, member, same⟩)
      have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
          (prior : ∃ added : List ObjectPublication,
            added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues
            ∧ acc.1.PublicationInventory property (published ++ added)
            ∧ ∀ publication ∈ published ++ added, acc.1.TaskMembershipAbsent publication.1)
          : ∃ added : List ObjectPublication,
            added.map Prod.snd = (groups.foldl successGroupStep acc).2.1.flatMap
              WorkQueueEvent.objectValues
            ∧ (groups.foldl successGroupStep acc).1.PublicationInventory property
                (published ++ added)
            ∧ ∀ publication ∈ published ++ added,
                (groups.foldl successGroupStep acc).1.TaskMembershipAbsent publication.1 := by
        induction groups generalizing acc with
        | nil => exact prior
        | cons group rest ih =>
            obtain ⟨added, values, next, excluded⟩ := prior
            exact ih _ (successGroupStep_publicationMemberships acc group values next excluded)
      obtain ⟨added, values, final, excluded⟩ := loop node.task.groups (_, [], {})
        ⟨[], rfl, by simpa only [List.append_nil] using
          State.PublicationInventory.mk inventory.unique inventory.provenance integrated,
          by simpa only [List.append_nil] using integratedAbsent⟩
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · refine ⟨[], rfl, ?_, ?_⟩
        · simpa only [List.append_nil] using State.PublicationInventory.mk inventory.unique
            inventory.provenance (inventory.stored.removeTask occurrence)
        · simpa only [List.append_nil]
            using (fun publication member =>
                    (absent publication member).removeTask occurrence)
      let released := node.task.groups.foldl successGroupStep
        (((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1, [], {})
      have activated := State.PublicationInventory.mk final.unique final.provenance
        (final.stored.startNewWork released.2.2)
      obtain ⟨later, laterValues, drained, removed⟩ := activated.drainReadyGroups_memberships
        (fun publication member => (excluded publication member).startNewWork released.2.2)
      refine ⟨added ++ later, ?_, ?_, ?_⟩
      · simp only [List.map_append, List.flatMap_append, values, laterValues]
        rfl
      · simpa only [List.append_assoc] using drained
      · simpa only [List.append_assoc] using removed

-----------------------------------------------------------------------------------------
-- Failure controls remove memberships; item arrivals integrate only new identities
-----------------------------------------------------------------------------------------

/-- A failed settlement cannot restore any previously delivered group membership.
Witness: global task removal, group cancellation, and error/counter-only record updates.
-/
theorem State.TaskMembershipAbsent.taskFailure {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (failed : Occurrence) (errors : Nat)
    : (queue.taskFailure failed errors).1.TaskMembershipAbsent occurrence := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else
          (acc.1.putGroupNode
            { node with pending := node.pending - 1
                        failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : acc.1.TaskMembershipAbsent occurrence)
      : (groups.foldl step acc).1.TaskMembershipAbsent occurrence := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · rename_i node found
          split
          · exact prior.removeGroup _
          · exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  unfold State.taskFailure
  split
  · exact absent
  · split
    · exact absent.removeTask failed
    · exact loop _ (_, []) (absent.removeTask failed)

/-- Item arrival preserves prior exclusions and removes newly drained object memberships.
Witness: fresh item-child integration, pruning and activation, followed by the joint drain
ledger. The leading item event is not an object publication.
-/
theorem State.PublicationInventory.streamItems_memberships {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (childrenFresh
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, task.occurrence ∉ published.map Prod.fst)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.streamItems stream items).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.streamItems stream items).1.PublicationInventory property
            (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            (queue.streamItems stream items).1.TaskMembershipAbsent publication.1 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (rest : List StreamItem) (included : rest.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.PublicationInventory property published)
      (excluded : ∀ publication ∈ published, acc.1.TaskMembershipAbsent publication.1)
      : (rest.foldl step acc).1.PublicationInventory property published
        ∧ ∀ publication ∈ published,
            (rest.foldl step acc).1.TaskMembershipAbsent publication.1 := by
    induction rest generalizing acc with
    | nil => exact ⟨prior, excluded⟩
    | cons item rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          ⟨
            prior.unique,
            prior.provenance,
            ((prior.stored.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork
              _
          ⟩
        intro publication member
        have integrated := (excluded publication member).maybeIntegrateWork item.work (by
          intro task taskMember same
          exact childrenFresh item (included List.mem_cons_self) task taskMember
            (List.mem_map.mpr ⟨publication, member, same⟩))
        exact (integrated.pruneEmptyGroups _).startNewWork _
  obtain ⟨folded, excluded⟩ := loop items (List.Subset.refl _) (queue, [], [], []) inventory absent
  unfold State.streamItems
  split
  · exact ⟨[], rfl, by simpa using inventory, by simpa using absent⟩
  · simpa only [List.flatMap_cons, WorkQueueEvent.objectValues, List.nil_append]
      using folded.drainReadyGroups_memberships excluded

/-- Every input handler preserves exclusion on its exact object publication inventory.
Witness: success/item handlers use fresh children and the joint flush ledger; failure and
stream-close controls only remove records or update non-membership fields.
-/
theorem State.PublicationInventory.handleGraphEvent_memberships
    {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    (event : GraphEvent)
    (allowed
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → property occurrence result.value ∧ occurrence ∉ published.map Prod.fst)
    (childrenFresh : ∀ task ∈ event.childTasks, task.occurrence ∉ published.map Prod.fst)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvent event).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvent event).1.PublicationInventory property
            (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            (queue.handleGraphEvent event).1.TaskMembershipAbsent publication.1 := by
  have preserved := inventory.stored.handleGraphEvent event allowed
  cases event with
  | taskSuccess occurrence result =>
      exact inventory.taskSuccess_memberships absent occurrence result
        (allowed _ _ rfl).1 (allowed _ _ rfl).2 childrenFresh
  | taskFailure occurrence errors =>
      refine ⟨[], (queue.taskFailure_objectValues occurrence errors).symm, ?_, ?_⟩
      · simpa only [List.append_nil] using State.PublicationInventory.mk inventory.unique
          inventory.provenance preserved
      · simpa only [List.append_nil, State.handleGraphEvent]
          using (fun publication member =>
                  (absent publication member).taskFailure occurrence errors)
  | streamItems stream items =>
      apply inventory.streamItems_memberships absent stream items
      intro item member task taskMember
      exact childrenFresh task (List.mem_flatMap.mpr ⟨item, member, taskMember⟩)
  | streamSuccess stream =>
      refine ⟨[], ?_, ?_, ?_⟩
      · simp only [State.handleGraphEvent, State.streamSuccess]
        split <;> rfl
      · simpa only [List.append_nil] using State.PublicationInventory.mk inventory.unique
          inventory.provenance preserved
      · simp only [State.handleGraphEvent, State.streamSuccess, List.append_nil]
        split <;> exact absent
  | streamFailure stream errors =>
      refine ⟨[], ?_, ?_, ?_⟩
      · simp only [State.handleGraphEvent, State.streamFailure]
        split <;> rfl
      · simpa only [List.append_nil] using State.PublicationInventory.mk inventory.unique
          inventory.provenance preserved
      · simp only [State.handleGraphEvent, State.streamFailure, List.append_nil]
        split <;> exact absent

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
