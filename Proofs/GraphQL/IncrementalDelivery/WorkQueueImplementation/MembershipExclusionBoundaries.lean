import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionWitness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainValueCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldBoundaries

/-! Source and internal drain prefixes share one exact membership-exclusion ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exact offsets combine earlier source outputs with the current handler's labels
-----------------------------------------------------------------------------------------

/-- A bounded drain cannot emit more object values than the complete drain.
Witness: splitting its actual iteration budget gives an output-prefix decomposition.
-/
theorem State.drainReadyGroups_go_objectCount_le (queue : State) {steps fuel : Nat}
    (bounded : steps ≤ fuel)
    : ((State.drainReadyGroups.go steps queue).2.flatMap
        WorkQueueEvent.objectValues).length
      ≤ ((State.drainReadyGroups.go fuel queue).2.flatMap
          WorkQueueEvent.objectValues).length := by
  have split := State.drainReadyGroups_go_add steps (fuel - steps) queue
  rw [Nat.add_sub_of_le bounded] at split
  rw [split, List.flatMap_append, List.length_append]
  exact Nat.le_add_right _ _

private theorem split_labels {published : List ObjectPublication}
    {publication offset count full} (bounded : count ≤ full)
    (member : publication ∈ published.take (offset + count))
    : publication ∈ published.take offset
      ∨ publication ∈ ((published.drop offset).take full).take count := by
  rw [List.take_add] at member
  simpa only [List.mem_append, List.take_take, Nat.min_eq_left bounded] using member

/-- Earlier emitted occurrences are excluded and fresh against the next child chunk.
Witness: restrict the original ledger, use its permanent registry, and derive child
freshness from the existing producer/source laws. No matching is selected again.
-/
theorem createWorkQueue_beforeHandlerMemberships {work before event after published}
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ event :: after) published)
    (valid : ValidGraphEvents work (before ++ event :: after))
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      ∀ publication ∈
        published.take
          (((State.initialize (Work.fromExecution work)).rawEventReplay before).2.flatMap
            WorkQueueEvent.objectValues).length,
        current.TaskMembershipAbsent publication.1
        ∧ ∀ child ∈ event.childTasks, publication.1 ≠ child.occurrence := by
  intro current publication member
  have earlier : before.IsPrefix (before ++ event :: after) := List.prefix_append _ _
  have registered := (covered.prefix before (event :: after)).registered publication member
  have ready := (createWorkQueue_replayGraphEvents_producerOrder (valid.prefix earlier)).1
  obtain ⟨matching, fresh, _⟩ := valid.atPrefix (show
    (before ++ [event]).IsPrefix (before ++ event :: after) from ⟨after, by simp⟩)
  refine ⟨
    createWorkQueue_replay_membershipsAbsent covered valid earlier publication member,
    ?_
  ⟩
  intro child incoming same
  exact matching.childTask_not_registered ready fresh incoming (same ▸ registered)

-----------------------------------------------------------------------------------------
-- Both value-producing handlers exclude the full history at every ready-drain boundary
-----------------------------------------------------------------------------------------

/-- Each owner-fold boundary excludes exactly the full history already emitted there.
Witness: preserve older source labels through fresh preparation and the processed owners;
use the common handler certificate for new labels. Taking the full handler ledger at the
actual prefix count cannot borrow a later owner or drain publication.
-/
theorem createWorkQueue_taskSuccess_foldMemberships
    {work before occurrence result after published incoming}
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .taskSuccess occurrence result :: after) published)
    (valid : ValidGraphEvents work (before ++ .taskSuccess occurrence result :: after))
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      current.taskNode? occurrence = some incoming
      → current.taskHasHealthyOwner incoming.task = true
      → ∀ steps,
          steps ≤ incoming.task.groups.length
          → let boundary :=
              (incoming.task.groups.take steps).foldl successGroupStep (prepared, [], {})
            ∀ publication ∈
              published.take
                ((((State.initialize (Work.fromExecution work)).rawEventReplay
                    before).2.flatMap
                    WorkQueueEvent.objectValues).length
                  + (boundary.2.1.flatMap WorkQueueEvent.objectValues).length),
              boundary.1.TaskMembershipAbsent publication.1 := by
  intro current stored prepared found healthy steps bounded boundary publication member
  have count := successGroupFold_objectCount_take_le incoming.task.groups (prepared, [], {}) steps
  have full : (boundary.2.1.flatMap WorkQueueEvent.objectValues).length
      ≤ ((current.handleGraphEvent (.taskSuccess occurrence result)).2.flatMap
          WorkQueueEvent.objectValues).length := by
    rw [State.handleGraphEvent, current.taskSuccess_eq occurrence result incoming found]
    simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      List.flatMap_append, List.length_append]
    exact Nat.le_trans count (Nat.le_add_right _ _)
  rcases split_labels full member with old | new
  · obtain ⟨absent, fresh⟩ :=
      createWorkQueue_beforeHandlerMemberships covered valid publication old
    have installed := absent.putTaskNode { incoming with value := some result.value }
    have integrated := installed.maybeIntegrateWork result.work fresh (some occurrence)
    exact integrated.successGroupFold (incoming.task.groups.take steps) [] {}
  · exact ((covered.atPrefixMemberships before (.taskSuccess occurrence result) after)
      incoming found healthy).ownerFold steps bounded publication new

/-- A task-success drain excludes every object published so far on the original ledger.
Witness: earlier-handler labels survive fresh preparation and the owner fold; the retained
handler-slice certificate clears its own publications. Exact raw counts join both prefixes.
This statement includes the owner fold's outputs but not its individual internal boundaries.
-/
theorem createWorkQueue_taskSuccess_drainMemberships
    {work before occurrence result after published incoming}
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .taskSuccess occurrence result :: after) published)
    (valid : ValidGraphEvents work (before ++ .taskSuccess occurrence result :: after))
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := released.1.startNewWork released.2.2
      current.taskNode? occurrence = some incoming
      → current.taskHasHealthyOwner incoming.task = true
      → ∀ steps,
          steps ≤ active.groupNodes.length
          → ∀ publication ∈
              published.take
                ((((State.initialize (Work.fromExecution work)).rawEventReplay
                    before).2.flatMap
                    WorkQueueEvent.objectValues).length
                  + ((released.2.1 ++ (State.drainReadyGroups.go steps active).2).flatMap
                      WorkQueueEvent.objectValues).length),
              (State.drainReadyGroups.go steps active).1.TaskMembershipAbsent
                publication.1 := by
  intro current stored prepared released active found healthy steps bounded publication member
  have count := active.drainReadyGroups_go_objectCount_le bounded
  have full : ((released.2.1 ++ (State.drainReadyGroups.go steps active).2).flatMap
      WorkQueueEvent.objectValues).length
      ≤ ((current.handleGraphEvent (.taskSuccess occurrence result)).2.flatMap
          WorkQueueEvent.objectValues).length := by
    rw [State.handleGraphEvent, current.taskSuccess_eq occurrence result incoming found]
    simpa only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      List.flatMap_append, List.length_append, State.drainReadyGroups,
      stored, prepared, released, active] using Nat.add_le_add_left count
        (released.2.1.flatMap WorkQueueEvent.objectValues).length
  rcases split_labels full member with old | new
  · obtain ⟨absent, fresh⟩ :=
      createWorkQueue_beforeHandlerMemberships covered valid publication old
    have stored := absent.putTaskNode { incoming with value := some result.value }
    have integrated := stored.maybeIntegrateWork result.work fresh (some occurrence)
    apply State.TaskMembershipAbsent.drainReadyGroups_go
    exact (integrated.successGroupFold incoming.task.groups [] {}).startNewWork _
  · exact ((covered.atPrefixMemberships before (.taskSuccess occurrence result) after)
      incoming found healthy).drain steps bounded publication new

/-- An active item handler excludes the full object history at every internal drain boundary.
Witness: source freshness preserves all earlier labels through item preparation, while
the exact handler slice clears new drain publications. The leading stream event has zero
object-value offset, even when it carries child notices.
-/
theorem createWorkQueue_streamItems_drainMemberships
    {work before stream items after published}
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .streamItems stream items :: after) published)
    (valid : ValidGraphEvents work (before ++ .streamItems stream items :: after))
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared := current.preparedStreamItems items
      current.rootStreams.contains stream.ref = true
      → ∀ steps,
          steps ≤ prepared.groupNodes.length
          → ∀ publication ∈
              published.take
                ((((State.initialize (Work.fromExecution work)).rawEventReplay
                    before).2.flatMap
                    WorkQueueEvent.objectValues).length
                  + ((State.drainReadyGroups.go steps prepared).2.flatMap
                      WorkQueueEvent.objectValues).length),
              (State.drainReadyGroups.go steps prepared).1.TaskMembershipAbsent
                publication.1 := by
  intro current prepared active steps bounded publication member
  have full : ((State.drainReadyGroups.go steps prepared).2.flatMap
      WorkQueueEvent.objectValues).length
      ≤ ((current.handleGraphEvent (.streamItems stream items)).2.flatMap
          WorkQueueEvent.objectValues).length := by
    rw [State.handleGraphEvent, current.streamItems_eq stream items]
    simpa only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons,
      WorkQueueEvent.objectValues, List.nil_append, State.drainReadyGroups,
      State.preparedStreamItems, prepared]
      using prepared.drainReadyGroups_go_objectCount_le bounded
  rcases split_labels full member with old | new
  · obtain ⟨absent, fresh⟩ :=
      createWorkQueue_beforeHandlerMemberships covered valid publication old
    apply (absent.preparedStreamItems items ?_).drainReadyGroups_go steps
    intro item itemMember child childMember
    exact fresh child (List.mem_flatMap.mpr ⟨item, itemMember, childMember⟩)
  · exact (covered.atPrefixMemberships before (.streamItems stream items) after)
      active steps bounded publication new

-----------------------------------------------------------------------------------------
-- Actual carrier positions recover their own exclusion boundary, not a later endpoint
-----------------------------------------------------------------------------------------

/-- An actual owner-fold carrier excludes every earlier publication at its emitting boundary.
Witness: locate the successful owner step at the indexed carrier, then use full-history
exclusion at that step. The carrier has no object payload, so its strict object prefix is
exactly the emitting boundary's object prefix, including the flush preceding the notice.
-/
theorem createWorkQueue_taskSuccess_ownerCarrierMemberships
    {work before occurrence result after published incoming index group groups streams}
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .taskSuccess occurrence result :: after) published)
    (valid : ValidGraphEvents work (before ++ .taskSuccess occurrence result :: after))
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let output := (incoming.task.groups.foldl successGroupStep (prepared, [], {})).2.1
      current.taskNode? occurrence = some incoming
      → current.taskHasHealthyOwner incoming.task = true
      → output[index]? = some (.groupSuccess group groups streams)
      → ∃ steps,
          steps < incoming.task.groups.length
          ∧ let boundary :=
              (incoming.task.groups.take (steps + 1)).foldl successGroupStep
                (prepared, [], {})
            output.take (index + 1) = boundary.2.1
            ∧ ∀ publication ∈
                published.take
                  ((((State.initialize (Work.fromExecution work)).rawEventReplay
                      before).2.flatMap
                      WorkQueueEvent.objectValues).length
                    + ((output.take index).flatMap WorkQueueEvent.objectValues).length),
                boundary.1.TaskMembershipAbsent publication.1 := by
  intro current stored prepared output found healthy selected
  obtain ⟨steps, bounded, exactPrefix⟩ :=
    successGroupFold_carrier_boundary prepared incoming.task.groups selected
  refine ⟨steps, bounded, exactPrefix, ?_⟩
  have count : (((incoming.task.groups.take (steps + 1)).foldl successGroupStep
      (prepared, [], {})).2.1.flatMap WorkQueueEvent.objectValues).length
      = ((output.take index).flatMap WorkQueueEvent.objectValues).length := by
    rw [← exactPrefix]
    change ((output.take (index + 1)).flatMap WorkQueueEvent.objectValues).length = _
    simp only [List.take_add_one, selected, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, WorkQueueEvent.objectValues, List.append_nil]
  have excluded := createWorkQueue_taskSuccess_foldMemberships covered valid
    found healthy (steps + 1) (by omega)
  dsimp only [prepared, stored, current] at count
  simpa only [count] using excluded

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
