import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActions

/-! Valid source closures exclude later references to the same output stream ref. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- If the earlier action closes its stream, the later action must use another ref. -/
def StreamAction.Before (earlier later : StreamAction) : Prop :=
  earlier.2 = true → earlier.1 ≠ later.1

-----------------------------------------------------------------------------------------
-- Input freshness and stream readiness prohibit references after source closure
-----------------------------------------------------------------------------------------

/-- A closing source action contributes its ref to the source's finalization identities.
Witness: only stream-success and stream-failure constructors carry a true closure flag.
-/
theorem GraphEvent.streamAction_closed {event : GraphEvent} {action : StreamAction}
    (selected : event.streamAction = some action) (closed : action.2 = true)
    : action.1 ∈ event.identities.2 := by
  cases event <;> cases selected <;> simp_all [GraphEvent.identities]

/-- A ready, fresh source action refers to a ref not finalized by earlier source inputs.
Witness: item readiness excludes closed streams; closure freshness excludes a second close.
-/
theorem GraphEvent.streamAction_unclosed {work before event action}
    (fresh : GraphEvent.Fresh before event) (ready : GraphEvent.Ready work before event)
    (selected : GraphEvent.streamAction event = some action)
    : action.1 ∉ before.flatMap (fun prior => prior.identities.2) := by
  cases event with
  | taskSuccess | taskFailure => cases selected
  | streamItems stream items =>
      have same : (stream.ref, false) = action := Option.some.inj selected
      subst action
      obtain ⟨address, results, producer, dependencies, _, _, unclosed, _⟩ := ready
      exact unclosed
  | streamSuccess stream | streamFailure stream _ =>
      have same : (stream.ref, true) = action := Option.some.inj selected
      subst action
      exact fresh.2.2.2 stream.ref List.mem_cons_self

/-- Source stream actions never reference a previously finalized stream.
Witness: append induction on the existing source semantics, using readiness for items
and freshness for closures. No generated-work or executable-queue premise is needed.
-/
theorem ValidGraphEvents.streamActions_ordered {work events}
    (valid : ValidGraphEvents work events)
    : (events.filterMap GraphEvent.streamAction).Pairwise StreamAction.Before := by
  induction valid with
  | nil => exact .nil
  | @append before event valid matching fresh ready ih =>
      rw [List.filterMap_append]
      apply List.pairwise_append.mpr
      refine ⟨ih, ?_, ?_⟩
      · cases event <;> simp [List.filterMap_cons, GraphEvent.streamAction]
      · intro earlier inBefore later inLast closed same
        obtain ⟨prior, member, selected⟩ := List.mem_filterMap.mp inBefore
        obtain ⟨last, singleton, selectedLast⟩ := List.mem_filterMap.mp inLast
        have equal := List.mem_singleton.mp singleton
        subst last
        apply GraphEvent.streamAction_unclosed fresh ready selectedLast
        rw [← same]
        exact List.mem_flatMap.mpr ⟨prior, member,
          GraphEvent.streamAction_closed selected closed⟩

/-- Actual normalized stream actions inherit source closure order.
Witness: the real queue/publisher's ordered action subsequence and valid source order.
Ignored inputs and arbitrary response batches cannot introduce a post-closure reference.
-/
theorem createWorkQueue_runNormalized_streamActions_ordered {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : (((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.filterMap
        streamAction).Pairwise
        StreamAction.Before :=
  valid.streamActions_ordered.sublist
    (createWorkQueue_runNormalized_streamActions (Work.fromExecution work) batches)

-----------------------------------------------------------------------------------------
-- Item atomization repeats references but never inserts a stream closure
-----------------------------------------------------------------------------------------

/-- Every action in an event's atomic expansion is that event's original stream action.
Witness: splitting items repeats their unchanged non-closing action; other events are
unchanged or have no stream action. Empty value lists may erase an action.
-/
theorem publicationAtoms_streamAction_mem {event action}
    (member : action ∈ (publicationAtoms event).filterMap streamAction)
    : streamAction event = some action := by
  cases event with
  | groupValues group values =>
      simp [publicationAtoms, List.filterMap_map, streamAction] at member
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => cases member
      | case2 =>
          have same : action = (stream.ref, false) := List.mem_singleton.mp member
          subst action
          rfl
      | case3 value next rest ih =>
          rcases List.mem_cons.mp member with same | later
          · subst action; rfl
          · exact ih later
  | groupSuccess | groupFailure | workQueueTermination => cases member
  | streamSuccess stream | streamFailure stream _ =>
      have same : action = (stream.ref, true) := List.mem_singleton.mp member
      subst action
      rfl

/-- An event's atomic expansion contains no reference following a stream closure.
Witness: multiple item atoms are all non-closing; any closing event remains a singleton.
-/
theorem publicationAtoms_streamActions_ordered (event : Execution.WorkQueueEvent)
    : ((publicationAtoms event).filterMap streamAction).Pairwise StreamAction.Before := by
  cases event with
  | groupValues group values =>
      have empty
          : ((publicationAtoms (.groupValues group values)).filterMap streamAction)
            = [] := by
        simp [publicationAtoms, List.filterMap_map, streamAction, Function.comp_def]
      rw [empty]
      exact .nil
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => exact .nil
      | case2 => exact .cons (by simp) .nil
      | case3 value next rest ih =>
          exact .cons (fun _ _ impossible => False.elim (Bool.false_ne_true impossible)) ih
  | groupSuccess | groupFailure | workQueueTermination => exact .nil
  | streamSuccess | streamFailure => exact .cons (by simp) .nil

/-- Stream closure order survives splitting all normalized value events into atoms.
Witness: each expansion is ordered internally, and actions from distinct expansions
retain the original pairwise closure relation.
-/
theorem streamActions_ordered_publicationAtoms {events : List Execution.WorkQueueEvent}
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    : ((events.flatMap publicationAtoms).filterMap streamAction).Pairwise
        StreamAction.Before := by
  have original := List.pairwise_filterMap.mp ordered
  clear ordered
  induction original with
  | nil => exact .nil
  | @cons event rest cross tail ih =>
      rw [List.flatMap_cons, List.filterMap_append]
      apply List.pairwise_append.mpr
      refine ⟨publicationAtoms_streamActions_ordered event, ih, ?_⟩
      intro first memberFirst second memberSecond
      obtain ⟨atom, atomMember, selected⟩ := List.mem_filterMap.mp memberSecond
      obtain ⟨later, laterMember, inExpansion⟩ := List.mem_flatMap.mp atomMember
      exact cross later laterMember first (publicationAtoms_streamAction_mem memberFirst)
        second (publicationAtoms_streamAction_mem
          (List.mem_filterMap.mpr ⟨atom, inExpansion, selected⟩))

/-- Actual atomic output never references a stream after that stream's closure.
Witness: source-order preservation through the real queue, publisher, and item splitting.
This concerns stream closures only; excluding a same-ref group closure additionally uses
generated role separation and group-event provenance before deriving the full Open clause.
-/
theorem createWorkQueue_runNormalized_atomicStreamActions_ordered {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms).filterMap
        streamAction).Pairwise
        StreamAction.Before :=
  streamActions_ordered_publicationAtoms
    (createWorkQueue_runNormalized_streamActions_ordered valid)

-----------------------------------------------------------------------------------------
-- Strict output prefixes contain no earlier closure of the currently referenced stream
-----------------------------------------------------------------------------------------

/-- At a stream reference, its ref has no earlier successful or failed stream closure.
Witness: lift action order back to event positions; any closing action in the strict
prefix would require its ref to differ from the current reference's ref.
-/
theorem streamActions_ordered_atEvent {events : List Execution.WorkQueueEvent}
    {index event ref}
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (atEvent : events[index]? = some event) (reference : ref ∈ streamReferenceRefs event)
    : (ref, true) ∉ (events.take index).filterMap streamAction := by
  have current : ∃ closing, streamAction event = some (ref, closing) := by
    cases event <;> simp_all [streamReferenceRefs, streamAction]
  obtain ⟨closing, selected⟩ := current
  intro closed
  obtain ⟨prior, member, priorAction⟩ := List.mem_filterMap.mp closed
  obtain ⟨position, atPrefix⟩ := List.mem_iff_getElem?.mp member
  have bound : position < index := by
    have size := (List.getElem?_eq_some_iff.mp atPrefix).choose
    simp only [List.length_take] at size
    omega
  have atPrior := (List.getElem?_take_of_lt bound).symm.trans atPrefix
  obtain ⟨priorBound, priorEq⟩ := List.getElem?_eq_some_iff.mp atPrior
  obtain ⟨currentBound, currentEq⟩ := List.getElem?_eq_some_iff.mp atEvent
  have relation := (List.pairwise_filterMap.mp ordered).rel_getElem_of_lt
    priorBound currentBound bound
  rw [priorEq, currentEq] at relation
  exact relation (ref, true) priorAction (ref, closing) selected rfl rfl

/-- Each actual atomic stream reference has no stream closure with that ref in its prefix.
Witness: valid source order survives handler filtering, normalization, and atomization.
This supplies the stream-closure part of Open without assuming any publication matching,
failure witness, generated metadata, or source start check.
-/
theorem createWorkQueue_runNormalized_streamUnclosedAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index event ref}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (reference : ref ∈ streamReferenceRefs event)
    : (ref, true)
      ∉ ((((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms).take
          index).filterMap
          streamAction :=
  streamActions_ordered_atEvent
    (createWorkQueue_runNormalized_atomicStreamActions_ordered valid) atEvent reference

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
