import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting

/-! Both successful and failed group closures retain strictly prior pending notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Reuse root accounting while checking every closure, not only failed closures
-----------------------------------------------------------------------------------------

/-- Reference accounting transports along an eventwise inclusion of reference keys.
Witness: list induction retains the same notice accumulation and restricts each reference.
-/
theorem ReferencesAnnounced.restrict {α : Type} {notices references fewer : α → Keys}
    {initial events} (known : ReferencesAnnounced notices references initial events)
    (included : ∀ event ∈ events, (fewer event).Subset (references event))
    : ReferencesAnnounced notices fewer initial events := by
  induction events generalizing initial with
  | nil => trivial
  | cons event rest ih =>
      exact ⟨(included event List.mem_cons_self).trans known.1,
        ih known.2 (fun next member => included next (List.mem_cons_of_mem _ member))⟩

/-- A successful flush references only its already active closing group.
Witness: its exact closure-key projection is a singleton; values add no group closure.
-/
theorem State.finishGroupSuccess_closureNotices (queue : State) (node : GroupNode)
    (active : node.group.node.key ∈ queue.rootGroups)
    : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
        (queue.finishGroupSuccess node).2.1 := by
  apply ReferencesAnnounced.of_references
  rw [queue.finishGroupSuccess_groupClosureKeys]
  simpa [List.Subset] using active

/-- Each recursive drain closes groups only after their initial or emitted notices.
Witness: the selected node is active; successful closure exposes precisely the roots
accounted for by the existing notice ledger before the recursive drain continues.
-/
theorem State.drainReadyGroups_closureNotices (queue : State)
    : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
        queue.drainReadyGroups.2 := by
  have loop (fuel : Nat) (current : State)
      : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys current.rootGroups
          (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current with
    | zero => trivial
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · trivial
        · rename_i node selected
          obtain ⟨key, active, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : current.groupNode? key with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if candidate.failure.isSome || candidate.pending == 0 then
                some candidate else none) = some node at choice
              split at choice
              · cases Option.some.inj choice
                have root := current.groupNode?_key found ▸ active
                cases cached : node.failure with
                | none =>
                    exact (current.finishGroupSuccess_closureNotices node root).append
                      ((ih _).mono (current.finishGroupSuccess_groupFailureNotices node).1)
                | some errors =>
                    have first : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys
                        current.rootGroups [(current.finishGroupFailure node errors).2] :=
                      ⟨by simpa [State.finishGroupFailure, rawGroupClosureKeys,
                        List.Subset] using root, trivial⟩
                    exact first.append ((ih _).mono
                      (current.finishGroupFailure_groupFailureNotices node errors root).1)
              · contradiction
  exact loop _ queue

/-- Task failure inherits closure announcements from its existing failed-closure proof.
Witness: this handler emits no successful group carrier, so both reference projections agree.
-/
theorem State.taskFailure_closureNotices (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
        (queue.taskFailure occurrence errors).2 := by
  apply (queue.taskFailure_groupFailureNotices occurrence errors).2.restrict
  intro event member
  cases event with
  | groupSuccess group groups streams =>
      exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups streams
        member)
  | groupFailure => exact List.Subset.refl _
  | groupValues | streamValues | streamSuccess | streamFailure | workQueueTermination =>
      simp [rawGroupClosureKeys, List.Subset]

/-- A task-success contributor fold closes only active groups before starting its children.
Witness: the executable root guard licenses each singleton closure; accumulated child
notices justify the final activation and its recursively drained completions.
-/
theorem State.taskSuccess_closureNotices (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
        (queue.taskSuccess occurrence result).2 := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found, ReferencesAnnounced]
  | some node =>
      let stored := queue.putTaskNode { node with value := some result.value }
      let integrated := stored.maybeIntegrateWork result.work (some occurrence)
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List WorkQueueEvent × NewWork)
          (roots : acc.1.rootGroups.Subset queue.rootGroups)
          (notices : acc.2.2.newGroups.map Execution.DeliveryNode.key
            = acc.2.1.flatMap rawGroupNoticeKeys)
          (prior : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys
            queue.rootGroups acc.2.1)
          : (groups.foldl successGroupStep acc).1.rootGroups.Subset queue.rootGroups
            ∧ (groups.foldl successGroupStep acc).2.2.newGroups.map Execution.DeliveryNode.key
              = (groups.foldl successGroupStep acc).2.1.flatMap rawGroupNoticeKeys
            ∧ ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
                (groups.foldl successGroupStep acc).2.1 := by
        induction groups generalizing acc with
        | nil => exact ⟨roots, notices, prior⟩
        | cons group rest ih =>
            rw [List.foldl_cons]
            dsimp only [successGroupStep]
            split
            · exact ih _ roots notices prior
            · rename_i descriptor selected
              split
              · rename_i ready
                have active : descriptor.group.node.key ∈ acc.1.rootGroups := by
                  have key := acc.1.groupNode?_key selected
                  simp only [Bool.and_eq_true, List.contains_iff_mem] at ready
                  exact key ▸ ready.1.1
                refine ih _ ((State.finishGroupSuccess_rootsSubset _ _).trans roots) ?_ ?_
                · simp only [List.map_append, List.flatMap_append, notices,
                    State.finishGroupSuccess_groupNotices]
                · let updated := { descriptor with pending := descriptor.pending - 1 }
                  have closing := State.finishGroupSuccess_closureNotices
                    (acc.1.putGroupNode updated) updated active
                  exact prior.append (closing.mono
                    (fun key member => List.mem_append_left _ (roots member)))
              · exact ih _ roots notices prior
      have initial : integrated.1.rootGroups = queue.rootGroups :=
        State.maybeIntegrateWork_rootGroups _ _ _
      obtain ⟨roots, notices, prior⟩ := loop node.task.groups (integrated.1, [], {})
        (by rw [initial]; exact List.Subset.refl _) rfl trivial
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · trivial
      · let folded := node.task.groups.foldl successGroupStep (integrated.1, [], {})
        apply prior.append ((State.drainReadyGroups_closureNotices _).mono ?_)
        rw [(folded.1.startNewWork_groupCore _).2.2, notices]
        intro key member
        exact (List.mem_append.mp member).elim
          (fun old => List.mem_append_left _ (roots old))
          (fun fresh => List.mem_append_right _ fresh)

/-- An item carrier announces every newly active group before the following closure drain.
Witness: child integration preserves old roots and accumulates new roots in the carrier;
the carrier itself references no closing group, so all drain references are strictly later.
-/
theorem State.streamItems_closureNotices (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
        (queue.streamItems stream items).2 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.rootGroups
        = queue.rootGroups ++ acc.2.1.map Execution.DeliveryNode.key)
      : (more.foldl step acc).1.rootGroups
        = queue.rootGroups ++ (more.foldl step acc).2.1.map Execution.DeliveryNode.key := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih
        dsimp only [step]
        rw [(State.startNewWork_groupCore _ _).2.2, State.pruneEmptyGroups_rootGroups,
          State.maybeIntegrateWork_rootGroups, prior, List.map_append, List.append_assoc]
  unfold State.streamItems
  split
  · trivial
  · let folded := items.foldl step (queue, [], [], [])
    have roots := loop items (queue, [], [], []) (by simp)
    refine ⟨by simp [rawGroupClosureKeys, List.Subset], ?_⟩
    change ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys
      (queue.rootGroups ++ folded.2.1.map Execution.DeliveryNode.key) folded.1.drainReadyGroups.2
    rw [← roots]
    exact folded.1.drainReadyGroups_closureNotices

/-- Every source handler emits group closures with strictly prior notices.
Witness: the task/item proofs cover all group closures; stream closures reference no groups.
-/
theorem State.handleGraphEvent_closureNotices (queue : State) (event : GraphEvent)
    : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
        (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_closureNotices occurrence result
  | taskFailure occurrence errors =>
      exact queue.taskFailure_closureNotices occurrence errors
  | streamItems stream items => exact queue.streamItems_closureNotices stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [ReferencesAnnounced, rawGroupClosureKeys, List.Subset]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [ReferencesAnnounced, rawGroupClosureKeys, List.Subset]

-----------------------------------------------------------------------------------------
-- Source replay, batching, and publisher normalization preserve that ordering
-----------------------------------------------------------------------------------------

/-- Sequential source replay preserves notice-before-closure ordering across handlers.
Witness: existing active-root accounting transports the next handler's initial notices.
-/
theorem State.rawEventReplay_closureNotices (queue : State) (events : List GraphEvent)
    : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
        (queue.rawEventReplay events).2 := by
  induction events generalizing queue with
  | nil => trivial
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact (queue.handleGraphEvent_closureNotices event).append
        ((ih _).mono (queue.handleGraphEvent_groupFailureNotices event).1)

/-- Batch termination adds no group reference and preserves the replay notice law.
Witness: the real batch wrapper either emits nothing or appends only its terminal marker.
-/
theorem State.handleGraphEvents_closureNotices (queue : State) (events : List GraphEvent)
    : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys queue.rootGroups
        (queue.handleGraphEvents events).2 := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · trivial
  · have prior := queue.rawEventReplay_closureNotices events
    dsimp only
    split
    · exact prior.append ⟨by simp [rawGroupClosureKeys, List.Subset], trivial⟩
    · exact prior

/-- Publisher normalization preserves both kinds of notice-before-closure references.
Witness: group notices and closing keys have exact projections through normalization.
-/
theorem ReferencesAnnounced.normalizeGroupClosures {initial events}
    (known : ReferencesAnnounced rawGroupNoticeKeys rawGroupClosureKeys initial events)
    (publisher : IncrementalPublisher)
    : ReferencesAnnounced groupNoticeKeys groupClosureKeys initial
        (publisher.normalizeBatch events).2 := by
  induction events generalizing initial publisher with
  | nil => trivial
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        rw [IncrementalPublisher.handleWorkQueueEvent_groupClosureKeys]
        exact known.1
      · rw [IncrementalPublisher.handleWorkQueueEvent_groupNotices]
        exact ih known.2 _

/-- All normalized group closures follow initial or earlier emitted group notices.
Witness: the concrete batch fold carries active-root support alongside closure ordering.
This theorem allows arbitrary raw work and source inputs; it is not output admission.
-/
theorem createWorkQueue_runNormalized_groupClosureNotices (work : Work)
    (batches : List (List GraphEvent))
    : ReferencesAnnounced groupNoticeKeys groupClosureKeys
        ((State.initialize work).initialGroups.map Execution.DeliveryNode.key)
        ((State.initialize work).runNormalized batches).2.flatten := by
  let initial := (State.initialize work).initialGroups.map Execution.DeliveryNode.key
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (roots : acc.1.rootGroups.Subset (initial ++ acc.2.2.flatten.flatMap groupNoticeKeys))
      (known : ReferencesAnnounced groupNoticeKeys groupClosureKeys initial acc.2.2.flatten)
      : ReferencesAnnounced groupNoticeKeys groupClosureKeys initial
          (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc with
    | nil => exact known
    | cons batch rest ih =>
        have localFacts := acc.1.handleGraphEvents_groupFailureNotices batch
        apply ih
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupNotices]
          intro key member
          rcases List.mem_append.mp (localFacts.1 member) with old | added
          · exact (List.mem_append.mp (roots old)).elim
              (fun root => List.mem_append_left _ root)
              (fun prior => List.mem_append_right _ (List.mem_append_left _ prior))
          · exact List.mem_append_right _ (List.mem_append_right _ added)
        · rw [normalizedStep_flatten]
          exact known.append
            (((acc.1.handleGraphEvents_closureNotices batch).normalizeGroupClosures acc.2.1).mono
              roots)
  let queue := State.initialize work
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, [])
    (by rw [createWorkQueue_rootGroups]; simp [initial, List.Subset]) trivial

/-- Atomic expansion preserves strict prior notices for both group-completion kinds.
Witness: nonempty stream carriers retain their notices; every completion stays a singleton.
-/
theorem ReferencesAnnounced.groupClosureAtoms {initial events}
    (known : ReferencesAnnounced groupNoticeKeys groupClosureKeys initial events)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : ReferencesAnnounced groupNoticeKeys groupClosureKeys initial
        (events.flatMap publicationAtoms) := by
  induction events generalizing initial with
  | nil => trivial
  | cons event rest ih =>
      rw [List.flatMap_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        rw [publicationAtoms_groupClosureKeys]
        exact known.1
      · rw [publicationAtoms_groupNotices event (nonempty event List.mem_cons_self)]
        exact ih known.2 (fun event member => nonempty event (List.mem_cons_of_mem _ member))

/-- Every actual atomic group completion refers to an already announced key.
Witness: replay's closure-notice law and nonempty value expansion identify a strictly
earlier notice, including carriers and closures produced within the same source handler.
-/
theorem createWorkQueue_runNormalized_groupClosureAnnouncedAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index event key}
    (selected
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (closed : key ∈ groupClosureKeys event)
    : let queue := State.initialize (Work.fromExecution work)
      key
      ∈ announcedKeys
          ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.key)
          (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
            index) := by
  have known := ((createWorkQueue_runNormalized_groupClosureNotices (Work.fromExecution work)
    batches).groupClosureAtoms (createWorkQueue_runNormalized_nonemptyValues valid).2).atEvent
      selected closed
  rcases List.mem_append.mp known with initial | prior
  · apply List.mem_append_left
    rw [List.map_append]
    exact List.mem_append_left _ initial
  · apply List.mem_append_right
    obtain ⟨carrier, member, noticed⟩ := List.mem_flatMap.mp prior
    apply List.mem_flatMap.mpr ⟨carrier, member, ?_⟩
    cases carrier <;> simp_all [groupNoticeKeys, eventPending, List.map_append]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
