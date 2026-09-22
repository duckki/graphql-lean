import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveObjectStreamHealth

/-! Every successfully published item is safe under one actual mixed failure witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Earlier source labels become strictly earlier publications, without payload comparison
-----------------------------------------------------------------------------------------

/-- Every item from an earlier source prefix is already published at a sufficient cutoff.
Witness: source validity identifies item labels; their ordered inventory prefix fits the
output's item count and the unchanged matching publishes exactly those retained labels.
-/
theorem sourceItem_published_before {work received matching index address ordinal}
    {before : List GraphEvent} {events : List Execution.WorkQueueEvent}
    (valid : ValidGraphEvents work received) (prior : before.IsPrefix received)
    (count
      : (before.flatMap GraphEvent.itemPublications).length
        ≤ ((events.take index).flatMap normalizedItemValues).length)
    (prefixes
      : ∀ position occurrence,
          occurrence
            ∈ ((received.flatMap GraphEvent.itemPublications).map Prod.fst).take
                ((events.take position).flatMap normalizedItemValues).length
          → Published matching (events.take position) occurrence)
    (success : Occurrence.item address ordinal ∈ before.flatMap GraphEvent.successes)
    : Published matching (events.take index) (.item address ordinal) := by
  have member := (valid.prefix prior).itemSuccess_publication success
  obtain ⟨after, same⟩ := prior
  apply prefixes index
  apply List.take_subset_take_left _ count
  rw [← same, List.flatMap_append, List.map_append]
  simpa only [← List.length_map (f := Prod.fst), List.take_left] using member

/-- Local owner health and safe successful producers exclude every cancellation cause.
Witness: inspect the original failure cut; owner failure contradicts health, while fixed
successful outcomes and supplied producer safety exclude both producer cases.
-/
theorem task_uncancelled_of_successfulProducerSafety
    {work matching events failures occurrence owners producer payload key}
    (known : TaskAt work occurrence owners producer payload) (owner : key ∈ owners)
    (healthy : ¬NodeFailed work matching events failures key)
    (failedPayloads
      : ∀ cut task,
          (cut, task) ∈ failures
          → ∃ owners producer payload,
              TaskAt work task owners producer payload ∧ payload.failure.isSome = true)
    (succeeded : ∀ source, producer = some source → TaskSucceeds work source)
    (safe
      : ∀ source,
          producer = some source → ¬TaskCancelled work matching events failures source)
    : ¬TaskCancelled work matching events failures occurrence := by
  rintro ⟨cut, member, reached, cause⟩
  cases cause with
  | owners other _ _ failed =>
      obtain ⟨_, _, descriptor⟩ := other
      exact healthy ⟨cut, member, reached,
        failed key ((known.unique descriptor).1 ▸ owner)⟩
  | producerFailed other _ recorded =>
      obtain ⟨_, _, descriptor⟩ := other
      exact taskSucceeds_not_failedBefore
        (succeeded _ (known.unique descriptor).2.1) failedPayloads recorded
  | producerCancelled other _ cancelled =>
      obtain ⟨_, _, descriptor⟩ := other
      exact safe _ (known.unique descriptor).2.1 ⟨cut, member, reached, cancelled⟩

-----------------------------------------------------------------------------------------
-- One output-position induction handles root, item-produced, and object-produced streams
-----------------------------------------------------------------------------------------

/-- All actual published items are historically uncancelled under the common mixed cuts.
Witness: strong induction on publication position. Root and item-produced streams have
empty defer dependencies; their producer publications are earlier. Object-produced streams
use actual release health and the source-prefix count bridge, which turns every remaining
item-safety premise into an earlier publication. A value protects itself from later cuts.
No admitted history, licensed failure inventory, or restriction on mixed nesting is assumed.
-/
theorem ExecutedWork.publishedItems_safe_mixed
    {work batches streams failures matching}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streams)
    (partition
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        failures.Perm
          (streams
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher batches).2.2)))
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (exactValues
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (ready
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → ∀ stream dependencies producer,
              stream.key ∈ streamReferenceKeys event
              → NodeAt work stream .stream dependencies producer
              → ∀ source,
                  producer = some source → Published matching (atoms.take index) source)
    (prefixes
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index occurrence,
          occurrence
            ∈ ((batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
                ((atoms.take index).flatMap normalizedItemValues).length
          → Published matching (atoms.take index) occurrence)
    : let atoms :=
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms
      ∀ address ordinal,
        Published matching atoms (.item address ordinal)
        → ¬TaskCancelled work matching atoms failures (.item address ordinal) := by
  let atoms := ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten.flatMap
    publicationAtoms
  change ∀ address ordinal, Published matching atoms (.item address ordinal)
    → ¬TaskCancelled work matching atoms failures (.item address ordinal)
  have objectKnown : ∀ entry ∈ sourceObjectFailureCuts 0
      ((State.initialize (Work.fromExecution work)).eligibleFailureBlocks
        ((State.initialize (Work.fromExecution work)).sourceRunBlocks
          { active := (State.initialize (Work.fromExecution work)).initialGroups ++
              (State.initialize (Work.fromExecution work)).initialStreams } batches).2.2),
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, known, _⟩ :=
      createWorkQueue_eligibleObjectFailureCuts_origin generated valid entry member
    exact ⟨owners, producer, path, errors, known⟩
  have atPosition : ∀ index event address ordinal,
      atoms[index]? = some event → IsValue event → matching index = .item address ordinal
      → ¬TaskCancelled work matching atoms failures (.item address ordinal) := by
    intro index
    induction index using Nat.strongRecOn with
    | ind index ih =>
        intro event address ordinal selected value matched
        have source := matched ▸ exactValues index event selected value
        have isItem : ∃ stream item groups children,
            event = .streamValues stream [item] groups children := by
          have annotation := source.itemAnnotation
          cases event with
          | streamValues stream items groups children =>
              cases items with
              | nil => cases source
              | cons item rest =>
                  cases rest with
                  | nil => exact ⟨stream, item, groups, children, rfl⟩
                  | cons next tail => cases source
          | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
          | workQueueTermination => cases annotation
        obtain ⟨stream, item, groups, children, rfl⟩ := isItem
        obtain ⟨owners, producer, known⟩ := source
        obtain ⟨ownerEq, dependencies, located⟩ := itemTask_owner_nodeAt known
        subst owners
        have earlierSafe {address ordinal}
            (published : Published matching (atoms.take index) (.item address ordinal))
            : ¬TaskCancelled work matching atoms failures (.item address ordinal) := by
          obtain ⟨position, prior, less, atPrior, isValue, same⟩ := published.before
          exact ih position less prior address ordinal atPrior isValue same
        have succeeded : ∀ parent, producer = some parent → TaskSucceeds work parent := by
          intro parent same
          obtain ⟨position, prior, _, atPrior, isValue, matched⟩ :=
            (ready index _ selected stream dependencies producer List.mem_cons_self located
              parent same).before
          exact matched ▸ (exactValues position prior atPrior isValue).succeeds
        cases producer with
        | none =>
            have empty : dependencies = [] := by
              obtain ⟨_, _, atStream⟩ := located
              exact Correctness.located_producer_context atStream
            exact cuts.item_safe_mixed partition objectKnown generated failedPayloads
              (createWorkQueue_runNormalized_atomicStreamActions_ordered valid)
              selected value matched ⟨_, _, known⟩ located known succeeded
              (by intro parent impossible; cases impossible) (.inl empty)
        | some parent =>
            cases parent with
            | item parentAddress parentOrdinal =>
                have empty : dependencies = [] := by
                  obtain ⟨_, _, atStream⟩ := located
                  exact Correctness.located_producer_context atStream
                exact cuts.item_safe_mixed partition objectKnown generated failedPayloads
                  (createWorkQueue_runNormalized_atomicStreamActions_ordered valid)
                  selected value matched ⟨_, _, known⟩ located known succeeded
                  (by intro parent same; cases same
                      exact earlierSafe (ready index _ selected stream dependencies _
                        List.mem_cons_self located _ rfl)) (.inl empty)
            | executionGroup parentAddress =>
                obtain ⟨before, input, after, split, _, count, bridge⟩ :=
                  generated.atomicObjectStreamHealthy_of_earlierItems valid started cuts partition
                    located selected rfl (by intros; intro impossible; cases impossible)
                    (matching := matching)
                have health := bridge (by
                  intro earlierAddress earlierOrdinal success cancelled
                  have published := sourceItem_published_before valid ⟨input :: after, split.symm⟩
                    count prefixes success
                  apply earlierSafe published
                  have full := cancelled.append (atoms.drop index)
                  simpa only [atoms, List.take_append_drop] using full)
                apply uncancelled_of_safe_publication selected value matched
                exact task_uncancelled_of_successfulProducerSafety known
                  List.mem_cons_self health.2 failedPayloads succeeded
                  (by intro parent same; cases same; exact health.1)
  intro address ordinal ⟨index, event, selected, value, matched⟩
  exact atPosition index event address ordinal selected value matched

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
