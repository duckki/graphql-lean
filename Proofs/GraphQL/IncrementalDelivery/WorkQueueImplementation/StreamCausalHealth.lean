import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SingletonOwners

/-! Historical owner health for generated streams with no producer or defer dependencies. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A root stream can fail only through one of its own items
-----------------------------------------------------------------------------------------

/-- A generated stream ref determines its enclosing defer dependencies.
Witness: stream-ref uniqueness fixes the structural address, and deterministic lookup
then identifies the enclosing-owner field. No publication or failure premise is used.
-/
theorem ExecutedWork.streamDependencies_unique {work : Execution.Work}
    (generated : ExecutedWork work)
    {first second firstOwners secondOwners firstProducer secondProducer}
    (firstAt : NodeAt work first .stream firstOwners firstProducer)
    (secondAt : NodeAt work second .stream secondOwners secondProducer)
    (sameRef : first.ref = second.ref)
    : firstOwners = secondOwners := by
  obtain ⟨left, firstItems, firstLocated⟩ := firstAt
  obtain ⟨right, secondItems, secondLocated⟩ := secondAt
  have sameAddress := generated.streamAddress_unique firstLocated secondLocated sameRef
  subst right
  have same := Option.some.inj (firstLocated.symm.trans secondLocated)
  exact congrArg WorkLocation.owners same

/-- A dependency-free root stream fails exactly when a contributing item has a visible cut.
Witness: role separation excludes group rules, unique empty dependencies exclude stream
dependency failure, and the root descriptor excludes producer cancellation. The reverse
direction uses the contributing task's own cut, so arbitrary cut order is permitted.
-/
theorem ExecutedWork.rootStream_nodeFailed_iff {work : Execution.Work}
    (generated : ExecutedWork work) {stream matching events failures}
    (root : NodeAt work stream .stream [] none)
    : NodeFailed work matching events failures stream.ref
      ↔ ∃ occurrence owners,
          TaskHasOwners work occurrence owners
          ∧ stream.ref ∈ owners
          ∧ occurrence ∈ failedBefore failures events.length := by
  constructor
  · rintro ⟨cut, member, reached, cause⟩
    cases cause with
    | task known owner finished =>
        exact ⟨_, _, known, owner, failedBefore_subset failures reached finished⟩
    | groupDependency known _ _ =>
        obtain ⟨group, producer, located, same⟩ := known
        exact False.elim (generated.groupStreamRefsDisjoint located root same)
    | streamDependencies known nonempty _ =>
        obtain ⟨node, producer, located, same⟩ := known
        exact False.elim (nonempty (generated.streamDependencies_unique located root same))
    | producers _ noRoot _ _ =>
        exact False.elim (noRoot ⟨stream, .stream, [], root, rfl⟩)
  · rintro ⟨occurrence, owners, ⟨producer, payload, known⟩, owner, finished⟩
    exact NodeFailed.task known owner finished

-----------------------------------------------------------------------------------------
-- Closure ordering rules out a prior failure of a still-used stream
-----------------------------------------------------------------------------------------

/-- No contributing stream-failure cut is visible at a nonfailure stream action.
Witness: an earlier same-ref failure would close the stream before this action, and a
cut at this position would make the current event a failure. This checks cut timing,
not just distinct failing occurrences or distinct response payloads.
-/
theorem StreamFailureCuts.no_failure_at_action
    {work events failures index event ref closing occurrence owners}
    (cuts : StreamFailureCuts work events failures)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (atEvent : events[index]? = some event)
    (action : streamAction event = some (ref, closing))
    (notFailure : ∀ node errors, event ≠ .streamFailure node errors)
    (known : TaskHasOwners work occurrence owners) (owner : ref ∈ owners)
    : occurrence ∉ failedBefore failures index := by
  intro failed
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp failed
  obtain ⟨member, reached⟩ := List.mem_filter.mp kept
  have reached : entry.1 ≤ index := by simpa using reached
  obtain ⟨node, errors, producer, selected, task⟩ := cuts.2 entry member
  rw [same] at task
  obtain ⟨otherProducer, payload, other⟩ := known
  rw [← (task.unique other).1] at owner
  have sameRef := List.mem_singleton.mp owner
  by_cases equal : entry.1 = index
  · rw [equal, atEvent] at selected
    exact notFailure node errors (Option.some.inj selected)
  · have earlier : entry.1 < index := by omega
    obtain ⟨leftBound, leftEq⟩ := List.getElem?_eq_some_iff.mp selected
    obtain ⟨rightBound, rightEq⟩ := List.getElem?_eq_some_iff.mp atEvent
    have relation := (List.pairwise_filterMap.mp ordered).rel_getElem_of_lt
      leftBound rightBound earlier
    rw [leftEq, rightEq] at relation
    exact relation (node.ref, true) rfl (ref, closing) action rfl sameRef.symm

/-- A root stream's values and successful closure remain healthy under all candidate cuts.
Witness: the structural failure characterization reduces historical health to absence of
an earlier contributing failure; ordered output actions establish that absence.
No Explained history, FailureWitness, or cancellation-safety assumption is required.
-/
theorem StreamFailureCuts.rootStream_healthy
    {work events failures index event stream closing matching}
    (cuts : StreamFailureCuts work events failures) (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (root : NodeAt work stream .stream [] none)
    (atEvent : events[index]? = some event)
    (action : streamAction event = some (stream.ref, closing))
    (notFailure : ∀ node errors, event ≠ .streamFailure node errors)
    : ¬NodeFailed work matching (events.take index) failures stream.ref := by
  intro failed
  obtain ⟨occurrence, owners, known, owner, member⟩ :=
    (generated.rootStream_nodeFailed_iff root).mp failed
  have length : (events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atEvent).1)
  rw [length] at member
  exact cuts.no_failure_at_action ordered atEvent action notFailure known owner member

-----------------------------------------------------------------------------------------
-- Root-stream readiness and successful closure no longer assume cancellation or health
-----------------------------------------------------------------------------------------

/-- A fresh ordered root-stream item satisfies the complete CanPublish predicate.
Witness: historical cancellation would fail its sole root owner, contradicting the
health derived from actual closure order. The absent producer leaves no readiness debt.
-/
theorem StreamFailureCuts.rootStream_canPublish
    {work events failures index stream values groups streams matching occurrence result}
    (cuts : StreamFailureCuts work events failures) (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (root : NodeAt work stream .stream [] none)
    (atEvent : events[index]? = some (.streamValues stream values groups streams))
    (known : TaskAt work occurrence [stream.ref] none (.item stream result))
    (fresh : ¬Published matching (events.take index) occurrence)
    (itemsOrdered
      : ∀ address first second,
          occurrence = .item address second
          → first < second
          → Published matching (events.take index) (.item address first))
    : CanPublish work matching (events.take index) failures occurrence none := by
  apply (itemTask_canPublish_iff_not_cancelled known fresh ?_ itemsOrdered failures).mpr
  · intro cancelled
    exact cuts.rootStream_healthy generated ordered root atEvent rfl
      (by intro node errors impossible; cases impossible) (cancelled.singleton_root_failed known)
  · intro dependencies located source impossible
    cases impossible

/-- An actual root stream's successful completion satisfies every EventAllowed clause.
Witness: prior notices give Open, ordered failure cuts give causal health, and exact
source-item coverage accounts for every contributor before the closing atom. The
matching is supplied unchanged, and no failure-licensing premise is introduced.
-/
theorem createWorkQueue_runNormalized_rootStreamSuccess_eventAllowed
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (matching : PublicationMatching)
    (exactValues
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (covered
      : ∀ occurrence ∈ (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst,
          Published matching
            (((State.initialize (Work.fromExecution work)).runNormalized
                batches).2.flatten.flatMap
              publicationAtoms) occurrence)
    {failures : FailureCuts}
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) failures)
    {index stream} (root : NodeAt work stream .stream [] none)
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.streamSuccess stream))
    : EventAllowed work
        (((State.initialize (Work.fromExecution work)).initialGroups
          ++ (State.initialize (Work.fromExecution work)).initialStreams).map
          Execution.DeliveryNode.ref) matching
        ((((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms).take
          index) failures (.streamSuccess stream) := by
  simp only [EventAllowed]
  rw [nodeFailed_filter (Nat.le_refl _)]
  exact ⟨
    ⟨[], none, root⟩,
    createWorkQueue_runNormalized_streamOpenAt generated valid atEvent List.mem_cons_self,
    cuts.rootStream_healthy generated
      (createWorkQueue_runNormalized_atomicStreamActions_ordered valid) root atEvent rfl
      (by intro node errors impossible; cases impossible),
    createWorkQueue_runNormalized_streamSuccess_accounted generated valid matching
      exactValues covered atEvent _
  ⟩

-----------------------------------------------------------------------------------------
-- Root-stream failures are licensed, not merely assigned candidate cut positions
-----------------------------------------------------------------------------------------

/-- Candidate cuts for root streams form a licensed FailureWitness.
Witness: singleton root ownership reduces prior cancellation to owner failure. Any
such failure would come from an earlier same-ref closing atom, excluded by closure
order. Reachability and open owners are independent source/notice facts.
This covers root-stream cuts only; produced-stream and object-cut licensing remain open.
-/
theorem StreamFailureCuts.rootStream_failureWitness
    {work events failures initial matching}
    (cuts : StreamFailureCuts work events failures) (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (roots
      : ∀ (index : Nat) (stream : Execution.DeliveryNode) (errors : Nat),
          events[index]? = some (.streamFailure stream errors)
          → NodeAt work stream .stream [] none)
    (supported
      : ∀ entry ∈ failures,
          Reachable work entry.2
          ∧ ∃ ref,
              TaskHasOwners work entry.2 [ref] ∧ Open initial (events.take entry.1) ref)
    : FailureWitness work initial matching events failures := by
  apply cuts.failureWitness_iff supported |>.mpr
  intro before cut occurrence after split cancelled
  have member : (cut, occurrence) ∈ failures := by simp [split]
  obtain ⟨stream, errors, producer, atEvent, task⟩ := cuts.2 _ member
  have root := roots cut stream errors atEvent
  obtain ⟨dependencies, located⟩ := (itemTask_owner_nodeAt task).2
  have producerNone := generated.streamProducer_unique located root rfl
  subst producer
  obtain ⟨earlier, owners, ⟨otherProducer, payload, known⟩, owner, failed⟩ :=
    (generated.rootStream_nodeFailed_iff root).mp
      (cancelled.singleton_root_failed task)
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp failed
  have prior := (List.mem_filter.mp kept).1
  have inCuts : entry ∈ failures := by rw [split]; exact List.mem_append_left _ prior
  obtain ⟨node, count, birth, selected, priorTask⟩ := cuts.2 entry inCuts
  rw [same] at priorTask
  rw [← (priorTask.unique known).1] at owner
  have sameRef := List.mem_singleton.mp owner
  have earlierCut : entry.1 < cut := by
    have increasing := cuts.ordered
    rw [split] at increasing
    exact increasing.rel_of_mem_append prior List.mem_cons_self
  exact streamFailure_refs_ne ordered selected atEvent earlierCut sameRef.symm

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
