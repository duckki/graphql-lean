import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootItemSafety

/-! Historical stream health from producer safety, without whole-history admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Safe successful producers leave only direct failure or defer dependency failure
-----------------------------------------------------------------------------------------

/-- A generated stream with a safe successful producer fails only through its items or
all its defer dependencies. Witness: invert failure at its original cut, identify the
stream's unique dependencies, and exclude producer cancellation using local safety.
No publication-support or admitted-history premise is needed.
-/
theorem ExecutedWork.streamFailure_causes_of_producerSafety
    {work matching events failures node dependencies producer}
    (generated : ExecutedWork work)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : NodeAt work node .stream dependencies producer)
    (succeeded : ∀ source, producer = some source → TaskSucceeds work source)
    (safe
      : ∀ source,
          producer = some source → ¬TaskCancelled work matching events failures source)
    (failure : NodeFailed work matching events failures node.ref)
    : (∃ occurrence owners,
        TaskHasOwners work occurrence owners
        ∧ node.ref ∈ owners
        ∧ occurrence ∈ failedBefore failures events.length)
      ∨ dependencies ≠ []
        ∧ ∀ dependency ∈ dependencies,
            NodeFailed work matching events failures dependency := by
  obtain ⟨cut, member, reached, cause⟩ := failure
  cases cause with
  | task task owner recorded =>
      exact .inl ⟨_, _, task, owner, failedBefore_subset failures reached recorded⟩
  | groupDependency descriptor _ _ =>
      obtain ⟨group, birth, located, same⟩ := descriptor
      exact False.elim (generated.groupStreamRefsDisjoint located known same)
  | streamDependencies descriptor nonempty failed =>
      obtain ⟨stream, birth, located, same⟩ := descriptor
      have equal := generated.streamDependencies_unique located known same
      exact .inr ⟨equal ▸ nonempty,
        fun ref included => ⟨cut, member, reached, failed ref (equal.symm ▸ included)⟩⟩
  | producers _ noRoot _ cancelled =>
      cases producer with
      | none => exact False.elim (noRoot ⟨node, .stream, dependencies, known, rfl⟩)
      | some source =>
          exact False.elim (safe source rfl ⟨cut, member, reached,
            cancelled source ⟨node, .stream, dependencies, known, rfl⟩
              (taskSucceeds_not_failedBefore (succeeded source rfl) failedPayloads)⟩)

/-- No direct failure and one healthy defer dependency keep a safe-produced stream healthy.
Witness: exclude the two original-cut failure causes; dependency-free streams need no
defer-owner certificate. The producer need not publish at every earlier failure cut.
-/
theorem ExecutedWork.streamHealthy_of_producerSafety
    {work matching events failures node dependencies producer}
    (generated : ExecutedWork work)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : NodeAt work node .stream dependencies producer)
    (succeeded : ∀ source, producer = some source → TaskSucceeds work source)
    (safe
      : ∀ source,
          producer = some source → ¬TaskCancelled work matching events failures source)
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → node.ref ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    (owners
      : dependencies = []
        ∨ ∃ ref ∈ dependencies, ¬NodeFailed work matching events failures ref)
    : ¬NodeFailed work matching events failures node.ref := by
  intro failure
  rcases generated.streamFailure_causes_of_producerSafety failedPayloads known succeeded
      safe failure with ⟨occurrence, refs, task, owner, recorded⟩ | ⟨nonempty, failed⟩
  · exact contributors occurrence refs task owner recorded
  · rcases owners with empty | ⟨ref, member, healthy⟩
    · exact nonempty empty
    · exact healthy (failed ref member)

-----------------------------------------------------------------------------------------
-- A published nested item inherits safety from its producer and defer support
-----------------------------------------------------------------------------------------

/-- A nested item is safe once its producer is safe and a defer dependency stays healthy
through its publication boundary. Witness: mixed stream-action order excludes direct
failure; the original-cut stream bridge excludes owner cancellation. Producer cases use
fixed success and historical safety, then the publication protects against later cuts.
These are local proof obligations, not additional host-source laws.
-/
theorem StreamFailureCuts.item_safe_mixed
    {work events streamCuts objectCuts failures matching address ordinal stream result
      dependencies producer index event}
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (generated : ExecutedWork work)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (selected : events[index]? = some event) (value : IsValue event)
    (matched : matching index = .item address ordinal)
    (exactValue : PublicationAt work (.item address ordinal) event)
    (located : NodeAt work stream .stream dependencies producer)
    (known
      : TaskAt work (.item address ordinal) [stream.ref] producer (.item stream result))
    (succeeded : ∀ source, producer = some source → TaskSucceeds work source)
    (safe
      : ∀ source,
          producer = some source → ¬TaskCancelled work matching events failures source)
    (owners
      : dependencies = []
        ∨ ∃ ref ∈ dependencies,
            ¬NodeFailed work matching (events.take index) failures ref)
    : ¬TaskCancelled work matching events failures (.item address ordinal) := by
  have action := exactValue.itemOwner_action ⟨producer, .item stream result, known⟩
    List.mem_cons_self
  have safeBefore : ∀ source, producer = some source
      → ¬TaskCancelled work matching (events.take index) failures source := by
    intro source parent cancelled
    apply safe source parent
    simpa only [List.take_append_drop] using cancelled.append (events.drop index)
  have healthy := generated.streamHealthy_of_producerSafety failedPayloads located
    succeeded safeBefore (fun occurrence refs task owner => ?_) owners
  · apply uncancelled_of_safe_publication selected value matched
    rintro ⟨cut, member, reached, cause⟩
    cases cause with
    | owners other _ _ failed =>
        obtain ⟨birth, payload, descriptor⟩ := other
        exact healthy ⟨cut, member, reached,
          failed stream.ref ((known.unique descriptor).1 ▸ List.mem_cons_self)⟩
    | producerFailed other _ recorded =>
        obtain ⟨refs, payload, descriptor⟩ := other
        exact taskSucceeds_not_failedBefore
          (succeeded _ (known.unique descriptor).2.1) failedPayloads recorded
    | producerCancelled other _ cancelled =>
        obtain ⟨refs, payload, descriptor⟩ := other
        exact safeBefore _ (known.unique descriptor).2.1 ⟨cut, member, reached, cancelled⟩
  · have length : (events.take index).length = index :=
      List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    rw [length]
    exact cuts.no_failure_at_action_mixed partition objects generated ordered located
      selected action (by intro node errors same; subst event; cases value) task owner

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
