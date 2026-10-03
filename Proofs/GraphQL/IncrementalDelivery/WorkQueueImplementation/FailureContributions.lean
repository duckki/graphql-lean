import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrorAccumulation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! Retained totals are sums of distinct earlier contributing source failures. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Error sums record actual source occurrences, not just a nonempty failure cache
-----------------------------------------------------------------------------------------

/-- `errors` is the sum of a nonempty, occurrence-distinct set of contributing failures
in `inputs`. This is source provenance, not completeness over all failures or a failure
cut.
-/
def GroupFailureTotal (work : Execution.Work) (inputs : List GraphEvent)
    (ref : NodeRef) (errors : Nat)
    : Prop :=
  ∃ contributions : List (Occurrence × Nat),
    contributions ≠ []
    ∧ (contributions.map Prod.fst).Nodup
    ∧ (contributions.map Prod.snd).sum = errors
    ∧ ∀ occurrence count,
        (occurrence, count) ∈ contributions
        → .taskFailure occurrence count ∈ inputs
          ∧ ∃ owners producer path,
              TaskAt work occurrence owners producer (.object path (.error count))
              ∧ ref ∈ owners

/-- An extended input history retains each earlier contributor and its exact count.
Witness: transport source membership, leaving the sum and occurrence uniqueness unchanged.
-/
theorem GroupFailureTotal.weaken {work before after ref errors}
    (total : GroupFailureTotal work before ref errors) (included : before.Subset after)
    : GroupFailureTotal work after ref errors := by
  obtain ⟨parts, nonempty, unique, sum, sources⟩ := total
  refine ⟨parts, nonempty, unique, sum, ?_⟩
  intro occurrence count member
  exact ⟨included (sources occurrence count member).1, (sources occurrence count member).2⟩

/-- A single matching failed task supplies a one-contributor total for each owner.
Witness: the singleton list has exactly the supplied error count and no duplicate task.
-/
theorem GroupFailureTotal.single {work inputs ref occurrence errors owners producer path}
    (source : GraphEvent.taskFailure occurrence errors ∈ inputs)
    (known : TaskAt work occurrence owners producer (.object path (.error errors)))
    (owner : ref ∈ owners)
    : GroupFailureTotal work inputs ref errors := by
  refine ⟨[(occurrence, errors)], by simp, by simp, by simp, ?_⟩
  intro task count member
  cases List.mem_singleton.mp member
  exact ⟨source, owners, producer, path, known, owner⟩

/-- A fresh matching failure increments an earlier total without duplicating its task.
Witness: prepend its occurrence/count pair; source freshness excludes every earlier pair.
-/
theorem GroupFailureTotal.accumulate
    {work before ref prior occurrence errors owners producer path}
    (total : GroupFailureTotal work before ref prior)
    (known : TaskAt work occurrence owners producer (.object path (.error errors)))
    (owner : ref ∈ owners)
    (fresh : (GraphEvent.taskFailure occurrence errors).Fresh before)
    : GroupFailureTotal work (before ++ [.taskFailure occurrence errors]) ref
        (prior + errors) := by
  obtain ⟨parts, _, unique, sum, sources⟩ := total
  have absent : occurrence ∉ parts.map Prod.fst := by
    intro member
    obtain ⟨⟨task, count⟩, member, same⟩ := List.mem_map.mp member
    dsimp only at same
    subst task
    have source := (sources occurrence count member).1
    apply fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
    exact List.mem_flatMap.mpr ⟨.taskFailure occurrence count, source,
      by simp [GraphEvent.identities]⟩
  refine ⟨
    (occurrence, errors) :: parts,
    by simp,
    by simpa only [List.map_cons, List.nodup_cons] using And.intro absent unique,
    ?_,
    ?_
  ⟩
  · simp [sum, Nat.add_comm]
  · intro task count member
    rcases List.mem_cons.mp member with same | earlier
    · cases same
      exact ⟨by simp, owners, producer, path, known, owner⟩
    · have source := sources task count earlier
      exact ⟨List.mem_append_left _ source.1, source.2⟩

/-- A total backed by one source failure cannot inflate that failure's count.
Witness: nonempty contributions select the sole input, and occurrence uniqueness rules
out a second contribution from the same task, even when the reported count is zero.
-/
theorem GroupFailureTotal.singleton_count {work ref total occurrence errors}
    (accounted : GroupFailureTotal work [.taskFailure occurrence errors] ref total)
    : total = errors := by
  obtain ⟨parts, nonempty, unique, sum, sources⟩ := accounted
  cases parts with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      have same (pair) (member : pair ∈ head :: tail) : pair = (occurrence, errors) := by
        obtain ⟨task, count⟩ := pair
        have equal := GraphEvent.taskFailure.inj
          (List.mem_singleton.mp (sources task count member).1)
        exact Prod.ext equal.1 equal.2
      have first := same head List.mem_cons_self
      subst head
      cases tail with
      | nil => simpa using sum.symm
      | cons second rest =>
          have next := same second (List.mem_cons_of_mem _ List.mem_cons_self)
          subst second
          simp at unique

-----------------------------------------------------------------------------------------
-- One graph-event step maintains exact source totals
-----------------------------------------------------------------------------------------

/-- Surviving task-failure caches are sums of distinct matching input failures.
Witness: the exact once-per-owner recurrence, registration provenance, and source
freshness.
Cached groups may survive; no all-failed-owners-retired assumption is used.
-/
theorem State.CachedErrorsSatisfy.taskFailure_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureTotal work before))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence) (errors : Nat)
    (source : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (fresh : (GraphEvent.taskFailure occurrence errors).Fresh before)
    : (queue.taskFailure occurrence errors).1.CachedErrorsSatisfy
        (GroupFailureTotal work (before ++ [.taskFailure occurrence errors])) := by
  have extended := totals.mono (fun _ _ total =>
    total.weaken (List.subset_append_left before [.taskFailure occurrence errors]))
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using extended
  | some task =>
      have registeredTask := registered task (List.mem_of_find?_eq_some found)
      have distinct := matching.contributorsNodup generated registeredTask
      have atTask := (State.taskNode?_some found).2
      obtain ⟨⟨_, _, _, _, known⟩, _⟩ := matching task.task registeredTask
      rw [atTask] at known
      obtain ⟨owners, producer, path, failed⟩ := source
      have sameOwners := (known.unique failed).1
      intro node live count cached
      obtain ⟨old, oldLive, sameRef, updated⟩ := queue.taskFailure_cachedErrors
        occurrence errors task found distinct live
      by_cases owns :
        queue.taskHasHealthyOwner task.task = true
          ∧ node.group.node.ref ∈ task.task.groups.map Execution.DeliveryNode.ref
      · have owner : node.group.node.ref ∈ owners := sameOwners ▸ owns.2
        simp only [owns] at updated
        have equal := Option.some.inj (cached.symm.trans updated)
        subst count
        cases prior : old.failure with
        | none =>
            simpa [prior] using GroupFailureTotal.single (by simp) failed owner
        | some previous =>
            have total := totals old oldLive previous prior
            rw [sameRef] at total
            simpa [prior] using total.accumulate failed owner fresh
      · simp only [owns, ↓reduceIte] at updated
        exact sameRef ▸ extended old oldLive count (updated.symm.trans cached)

/-- Every handler preserves exact source totals through a fresh matching input event.
Witness: only task failure adds a contribution; all other handlers preserve exact caches.
-/
theorem State.CachedErrorsSatisfy.handleGraphEvent_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureTotal work before))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    : (queue.handleGraphEvent event).1.CachedErrorsSatisfy
        (GroupFailureTotal work (before ++ [event])) := by
  have extended := totals.mono (fun _ _ total =>
    total.weaken (List.subset_append_left before [event]))
  cases event with
  | taskSuccess occurrence result => exact extended.taskSuccess occurrence result
  | taskFailure occurrence errors =>
      exact totals.taskFailure_totals generated registered matching occurrence errors source fresh
  | streamItems stream items => exact extended.streamItems stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact extended
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact extended

-----------------------------------------------------------------------------------------
-- Eventwise and normalized replay supply the invariant, without output admission
-----------------------------------------------------------------------------------------

/-- Source replay carries registration alongside its distinct-failure cache totals.
Witness: source-prefix induction threads registration and exact cache totals together.
Neither accepted starts nor scheduler conformance is required for this direction.
-/
private theorem ExecutedWork.replayGraphEvents_failureInventory {work : Execution.Work}
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      queue.CachedErrorsSatisfy (GroupFailureTotal work events)
      ∧ queue.StartedTasksRegistered
      ∧ queue.RegisteredTasksMatch work := by
  induction valid with
  | nil =>
      exact ⟨createWorkQueue_cachedErrors _ _, createWorkQueue_startedTasksRegistered _,
        createWorkQueue_fromSpec_registeredTasksMatch work⟩
  | @append before event valid matching fresh ready ih =>
      rw [State.replayGraphEvents_append]
      exact ⟨ih.1.handleGraphEvent_totals generated ih.2.1 ih.2.2 event matching fresh,
        ih.2.1.handleGraphEvent event, ih.2.2.handleGraphEvent event matching⟩

/-- Every cache after a valid source prefix sums distinct earlier owning-task failures.
Witness: the joint replay inventory supplies exact totals and proves its own registration
premises internally. No accepted-start, output-admission, or conformance premise is used.
-/
theorem ExecutedWork.replayGraphEvents_cachedFailureTotals {work : Execution.Work}
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).CachedErrorsSatisfy
        (GroupFailureTotal work events) :=
  (generated.replayGraphEvents_failureInventory valid).1

/-- Accepted normalized replay retains the same exact failure-total certificate.
Witness: normalization and batch termination affect no group cache in the eventwise state.
-/
theorem ExecutedWork.runNormalized_cachedFailureTotals {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.CachedErrorsSatisfy
        (GroupFailureTotal work batches.flatten) := by
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  exact generated.replayGraphEvents_cachedFailureTotals valid

/-- Every failed closure uses the current failed input or a certified earlier total.
Witness: the handler origin theorem and registered task descriptors identify the current
contribution; exact caches cover closures released by a later successful input.
-/
theorem State.CachedErrorsSatisfy.handleGraphEvent_outputTotal {queue : State}
    {work before} (totals : queue.CachedErrorsSatisfy (GroupFailureTotal work before))
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (event : GraphEvent) (matching : event.MatchesWork work) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.handleGraphEvent event).2)
    : GroupFailureTotal work (before ++ [event]) group.ref errors := by
  rcases queue.handleGraphEvent_groupFailure_origin event emitted with current | cached
  · obtain ⟨occurrence, task, rfl, found, owner⟩ := current
    have atTask := (State.taskNode?_some found).2
    obtain ⟨⟨_, _, _, _, known⟩, _⟩ := tasks task.task
      (registered task (List.mem_of_find?_eq_some found))
    rw [atTask] at known
    obtain ⟨owners, producer, path, failed⟩ := matching
    exact GroupFailureTotal.single (by simp) failed ((known.unique failed).1 ▸ owner)
  · obtain ⟨node, live, ref, cached⟩ := cached
    have total := totals node live errors cached
    rw [ref] at total
    exact total.weaken (List.subset_append_left before _)

/-- A failed closure after source replay reports a sum of distinct contributing failures.
Witness: the handler's current-task-or-prior-cache origin, with exact replay totals in the
cached branch. This is payload provenance, not an ordered output failure-cut witness.
-/
theorem ExecutedWork.replayGraphEvents_groupFailureTotal {work : Execution.Work}
    (generated : ExecutedWork work) {before : List GraphEvent}
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (matching : event.MatchesWork work) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (State.handleGraphEvent
            ((State.initialize (Work.fromExecution work)).replayGraphEvents before)
            event).2)
    : GroupFailureTotal work (before ++ [event]) group.ref errors := by
  obtain ⟨totals, registered, tasks⟩ := generated.replayGraphEvents_failureInventory valid
  exact totals.handleGraphEvent_outputTotal registered tasks event matching emitted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
