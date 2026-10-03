import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureLicensing

/-! Published root-stream items are safe throughout mixed failure histories. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Safety at the publication boundary is enough, without admitted output
-----------------------------------------------------------------------------------------

/-- A value safe immediately before publication stays safe throughout the supplied history.
Witness: earlier cancellation contradicts boundary safety; a later cut already contains
the value and contradicts the cancellation rule's unpublished premise. This does not
assume admission, a licensed inventory, or safety of other publications.
-/
theorem uncancelled_of_safe_publication
    {work matching events failures index event occurrence}
    (selected : events[index]? = some event) (value : IsValue event)
    (matched : matching index = occurrence)
    (safe : ¬TaskCancelled work matching (events.take index) failures occurrence)
    : ¬TaskCancelled work matching events failures occurrence := by
  rintro ⟨cut, member, reached, cause⟩
  by_cases earlier : cut ≤ index
  · apply safe
    refine ⟨cut, member, ?_, ?_⟩
    · have within := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.length_take]
      omega
    · simpa only [List.take_take, Nat.min_eq_left earlier] using cause
  · exact cause.unpublished
      ⟨index, event, (List.getElem?_take_of_lt (by omega)).trans selected, value, matched⟩

-----------------------------------------------------------------------------------------
-- Root stream order supplies that boundary even with object failures interleaved
-----------------------------------------------------------------------------------------

/-- A published root-stream item is historically uncancelled under the full mixed cuts.
Witness: exact publication provenance identifies its stream action; closure order and
group/stream role separation prove its root owner healthy at that position. Its own
publication then protects it at every later cut. Other values need no safety premise.
-/
theorem StreamFailureCuts.rootItem_safe_mixed
    {work events streamCuts objectCuts failures matching address ordinal stream result}
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (exactValues
      : ∀ index event,
          events[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (root : NodeAt work stream .stream [] none)
    (known : TaskAt work (.item address ordinal) [stream.ref] none (.item stream result))
    (published : Published matching events (.item address ordinal))
    : ¬TaskCancelled work matching events failures (.item address ordinal) := by
  obtain ⟨index, event, selected, value, matched⟩ := published
  have action := (matched ▸ exactValues index event selected value).itemOwner_action
    ⟨none, .item stream result, known⟩ List.mem_cons_self
  have healthy := cuts.rootStream_healthy_mixed (matching := matching)
    partition objects generated ordered root selected action
    (by intro node errors same; subst event; cases value)
  exact uncancelled_of_safe_publication selected value matched
    (fun cancelled => healthy (cancelled.singleton_root_failed known))

-----------------------------------------------------------------------------------------
-- Successful source items retain the publication inventory used by actual replay
-----------------------------------------------------------------------------------------

/-- A successful source item occurs in the source's exact item-publication inventory.
Witness: valid object successes cannot use item addresses; stream events retain every
item label in both projections. No output or scheduling premise is needed.
-/
theorem ValidGraphEvents.itemSuccess_publication {work received source index}
    (valid : ValidGraphEvents work received)
    (success : Occurrence.item source index ∈ received.flatMap GraphEvent.successes)
    : Occurrence.item source index
      ∈ (received.flatMap GraphEvent.itemPublications).map Prod.fst := by
  obtain ⟨event, member, included⟩ := List.mem_flatMap.mp success
  have matching := valid.eachMatches member
  rw [List.map_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨event, member, ?_⟩
  cases event with
  | taskSuccess task value =>
      have same := List.mem_singleton.mp included
      obtain ⟨owners, producer, known, _⟩ := matching
      rw [← same] at known
      cases StructuralEquivalence.taskAt_of_current known
  | streamItems stream items =>
      simpa only [GraphEvent.itemPublications, GraphEvent.successes, List.map_map,
        Function.comp_def]
        using included
  | taskFailure | streamSuccess | streamFailure => cases included

/-- Covered successful source items of root streams are safe under the mixed inventory.
Witness: source coverage provides their real publication, then root-item safety applies
under the same matching and cuts. The root restriction concerns this item, not the work
tree: deferred child groups and failures elsewhere remain permitted.
-/
theorem StreamFailureCuts.rootSourceItem_safe_mixed
    {work events streamCuts objectCuts failures matching received source index stream
      result}
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (exactValues
      : ∀ position event,
          events[position]? = some event
          → IsValue event
          → PublicationAt work (matching position) event)
    (valid : ValidGraphEvents work received)
    (covered
      : ∀ occurrence ∈ (received.flatMap GraphEvent.itemPublications).map Prod.fst,
          Published matching events occurrence)
    (root : NodeAt work stream .stream [] none)
    (known : TaskAt work (.item source index) [stream.ref] none (.item stream result))
    (success : Occurrence.item source index ∈ received.flatMap GraphEvent.successes)
    : ¬TaskCancelled work matching events failures (.item source index) :=
  cuts.rootItem_safe_mixed partition objects generated ordered exactValues root known
    (covered _ (valid.itemSuccess_publication success))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
