import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupObjectStreamHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulItemSafety

/-! Startup publications exclude cancellation under the same mixed failure cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Induction over actual startup publication positions protects every successful item.
Object-produced streams use their actual source support; root and item-produced streams
have empty defer dependencies. Earlier item prerequisites use the same publication matching.
No output admission or successful-item safety is assumed as a source contract.
-/
theorem ExecutedWork.startup_publishedItems_safe_mixed
    {work batches streams failures matching} (generated : ExecutedWork work)
    (startup : InitialStartup) (startupMatched : startup.MatchesWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    (cuts
      : StreamFailureCuts work
          ((((State.initialize (Work.fromExecution work) startup)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streams)
    (partition
      : failures.Perm (streams ++ startup.informativeObjectFailureCuts work batches))
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (exactValues
      : let atoms :=
          (((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (ready
      : let atoms :=
          (((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → ∀ stream dependencies producer,
              stream.ref ∈ streamReferenceRefs event
              → NodeAt work stream .stream dependencies producer
              → ∀ source,
                  producer = some source → Published matching (atoms.take index) source)
    (prefixes
      : let atoms :=
          (((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index occurrence,
          occurrence
            ∈ ((batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
                ((atoms.take index).flatMap normalizedItemValues).length
          → Published matching (atoms.take index) occurrence)
    : let atoms :=
        (((State.initialize (Work.fromExecution work) startup)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms
      ∀ address ordinal,
        Published matching atoms (.item address ordinal)
        → ¬TaskCancelled work matching atoms failures (.item address ordinal) := by
  let initial := State.initialize (Work.fromExecution work) startup
  let atoms := (initial.runNormalized batches).2.flatten
    |>.flatMap publicationAtoms
  change ∀ address ordinal, Published matching atoms (.item address ordinal)
    → ¬TaskCancelled work matching atoms failures (.item address ordinal)
  have objectKnown : ∀ entry ∈ startup.informativeObjectFailureCuts work batches,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨owners, producer, path, errors, known⟩ :=
      startup.objectReportingCuts_objectOrigin startupMatched generated valid entry
        ((selectObjectFailureCuts_sublist work [] _).subset member)
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
              (State.startup_runNormalized_atomicStreamActions_ordered startup valid)
              selected value matched ⟨_, _, known⟩ located known succeeded
              (by intro parent impossible; cases impossible) (.inl empty)
        | some parent =>
            cases parent with
            | item parentAddress parentOrdinal =>
                have empty : dependencies = [] := by
                  obtain ⟨_, _, atStream⟩ := located
                  exact Correctness.located_producer_context atStream
                exact cuts.item_safe_mixed partition objectKnown generated failedPayloads
                  (State.startup_runNormalized_atomicStreamActions_ordered startup valid)
                  selected value matched ⟨_, _, known⟩ located known succeeded
                  (by intro parent same; cases same
                      exact earlierSafe (ready index _ selected stream dependencies _
                        List.mem_cons_self located _ rfl)) (.inl empty)
            | executionGroup parentAddress =>
                obtain ⟨before, input, after, split, _, count, bridge⟩ :=
                  generated.startup_atomicObjectStreamHealthy_of_earlierItems startup startupMatched
                    valid started cuts partition
                    located selected rfl (by intros; intro impossible; cases impossible)
                    (matching := matching)
                have health := bridge (by
                  intro earlierAddress earlierOrdinal success cancelled
                  have published := sourceItem_published_before valid ⟨input :: after, split.symm⟩
                    count prefixes success
                  apply earlierSafe published
                  have full := cancelled.append (atoms.drop index)
                  simpa only [atoms, initial, List.take_append_drop] using full)
                apply uncancelled_of_safe_publication selected value matched
                exact task_uncancelled_of_successfulProducerSafety known
                  List.mem_cons_self health.2 failedPayloads succeeded
                  (by intro parent same; cases same; exact health.1)
  intro address ordinal ⟨index, event, selected, value, matched⟩
  exact atPosition index event address ordinal selected value matched

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
