import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RepresentedStopSafety
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

/-! Fixed-snapshot stop coverage: overlapping raw roots, stale links, and generated leases. -/

namespace AlternativeStopCoverageChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- A forest alone does not justify the shared node-count budget over several roots
-----------------------------------------------------------------------------------------

private def task : WorkQueueSemantics.Occurrence := .executionGroup [3]

private def raw : State :=
  {
    queue :=
      {
        groupNodes :=
          [
            { group := { node := ⟨0, [], none⟩ }, childGroups := [1] },
            { group := { node := ⟨1, [], none⟩, parent := some 0 }, childGroups := [2] },
            { group := { node := ⟨2, [], none⟩, parent := some 1 } },
            { group := { node := ⟨3, [], none⟩ }, tasks := [task] }
          ]
        rootGroups := [0, 1, 2, 3]
      }
  }

private def parents : Nat → WorkQueueSemantics.NodeRefs
  | 1 => [0]
  | 2 => [1]
  | _ => []

example : raw.queue.RemovalForest parents := by
  refine ⟨?_, ?_, ?_⟩
  · intro node member
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro node member key linked
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp_all [parents]
  · intro parent child parentMember childMember linked
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at parentMember childMember
    rcases parentMember with rfl | rfl | rfl | rfl
    all_goals rcases childMember with rfl | rfl | rfl | rfl
    all_goals simp_all

example : raw.queue.rootGroups.Nodup := by decide

-- Repeated live visits consume all five units before reaching the unrelated fourth root.
example : .task task ∉ raw.cleanupTargets := by cbv; intro impossible; cases impossible

example : ¬raw.queue.RootAntichain := by
  intro antichain
  have impossible : 0 = 1 := antichain 0 (by decide) 1 (by decide)
    (.child (by rfl) (by decide) (.self (by rfl)))
  omega

-----------------------------------------------------------------------------------------
-- Missing child keys do not consume live-visit fuel
-----------------------------------------------------------------------------------------

private def stale : State :=
  {
    queue :=
      {
        groupNodes :=
          [
            {
              group := { node := ⟨0, [], none⟩ }, childGroups := List.range' 10 100 ++ [1]
            },
            { group := { node := ⟨1, [], none⟩, parent := some 0 }, tasks := [task] }
          ]
        rootGroups := [0]
      }
  }

example : stale.queue.groupNodes.length + 1 = 3 := rfl
example : .task task ∈ stale.cleanupTargets := by cbv; exact .head _

-- Buffered links alone are vacuous for a raw orphan; generated owner existence is stronger.
private def orphan : ReferenceWorkQueue.State :=
  {
    taskNodes :=
      [{
        task := { occurrence := task, groups := [⟨3, [], none⟩] },
        value := some { path := [], data := [] }
      }]
  }

example : orphan.StoredTaskLinks := by intro node member stored group live; cases live

example : ¬orphan.BufferedOwnersPresent := by
  intro owners
  obtain ⟨key, contributes, present⟩ := owners _ List.mem_cons_self rfl
  cases present

-- A live owner is still insufficient in unrestricted raw states: it may be unrooted.
private def stranded : ReferenceWorkQueue.State :=
  {
    groupNodes := [{ group := { node := ⟨3, [], none⟩ }, tasks := [task] }],
    taskNodes := orphan.taskNodes,
    tasks := [{ occurrence := task, groups := [⟨3, [], none⟩] }]
  }

example : stranded.BufferedOwnersPresent := by
  intro node member _stored
  simp only [stranded, orphan, List.mem_singleton] at member
  subst node
  exact ⟨3, by decide, by decide⟩

example : ¬stranded.LiveContributorsCovered := by
  intro covered
  obtain ⟨root, active, _⟩ := covered _ List.mem_cons_self 3 (by decide) ⟨_, rfl⟩
  cases active

-----------------------------------------------------------------------------------------
-- The universal theorem reaches the independently acquired generated held source
-----------------------------------------------------------------------------------------

private def inputs : List (List GraphEvent) :=
  [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]

private abbrev replayed :=
  ((State.initialize SharedOwnerFailure.work).runNormalized inputs).1

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work inputs.flatten :=
  SharedOwnerFailure.valid_events.prefix
    ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩

private theorem started
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work inputs = true := by
  rw [SharedOwnerFailure.work_shape]
  cbv

private theorem covered : .stream 2 ∈ replayed.cleanupTargets := by
  let node := (replayed.queue.taskNode? SharedOwnerFailure.heldProducer).getD
    { task := { occurrence := SharedOwnerFailure.heldProducer, groups := [] } }
  have found : replayed.queue.taskNode? SharedOwnerFailure.heldProducer = some node := by
    dsimp only [node, replayed]
    rw [SharedOwnerFailure.work_shape]
    cbv
  have stored : node.value.isSome = true := by
    dsimp only [node, replayed]
    rw [SharedOwnerFailure.work_shape]
    cbv
  have reachable := GeneratedBufferedStopCoverage_holds SharedOwnerFailure.work inputs
    SharedOwnerFailure.executed valid started SharedOwnerFailure.heldProducer node found stored
  apply reachable
  rw [SharedOwnerFailure.work_shape]
  cbv
  exact .tail _ (.head _)

example : replayed.queue.rootGroups.Nodup ∧ replayed.queue.RootAntichain :=
  GeneratedStopRootTopology_holds SharedOwnerFailure.work inputs
    SharedOwnerFailure.executed valid started

private theorem representation
    : ResourcesRepresented replayed.queue SharedOwnerFailure.leases := by
  intro target owned
  by_cases same : target = .stream 2
  · subst target
    let node := (replayed.queue.taskNode? SharedOwnerFailure.heldProducer).getD
      { task := { occurrence := SharedOwnerFailure.heldProducer, groups := [] } }
    exact .bufferedStream
      (occurrence := SharedOwnerFailure.heldProducer) (node := node)
      (by dsimp only [node, replayed]; rw [SharedOwnerFailure.work_shape]; cbv)
      (by dsimp only [node, replayed]; rw [SharedOwnerFailure.work_shape]; cbv)
      (by dsimp only [node, replayed]; rw [SharedOwnerFailure.work_shape]; cbv; exact .head _)
  · simp [SharedOwnerFailure.leases, ResourceState.adopt, ResourceState.set,
      ResourceState.empty, same] at owned

private theorem coverage : StopCoverage replayed SharedOwnerFailure.leases :=
  generatedReplay_stopCoverage_of_representation SharedOwnerFailure.executed valid started
    SharedOwnerFailure.leases representation

-- The supplied acquisition/adoption trace is independent of the stop target calculation.
example
    : ResourceReplay ResourceState.empty
        [
          .acquire (.stream 2) (.producer SharedOwnerFailure.heldProducer),
          .adopt SharedOwnerFailure.heldProducer [.stream 2]
        ] SharedOwnerFailure.leases :=
  SharedOwnerFailure.handoff

example
    : ∀ target,
        (SharedOwnerFailure.leases.observeStop replayed).1 target ≠ .owned .queue :=
  (GeneratedRepresentedStopSafety_holds SharedOwnerFailure.work inputs
    SharedOwnerFailure.executed valid started SharedOwnerFailure.leases representation
    (by rw [SharedOwnerFailure.work_shape]; cbv)).2

-----------------------------------------------------------------------------------------
-- A legal acquisition history is not complete same-run record representation
-----------------------------------------------------------------------------------------

private def untracked : ResourceState :=
  ResourceState.empty.set (.stream 999) (.owned .queue)

example : ResourceReplay ResourceState.empty [.acquire (.stream 999) .queue] untracked :=
  .cons (.acquire _ _ _ rfl) (.nil _)

private theorem untracked_not_represented
    : ¬ResourcesRepresented replayed.queue untracked := by
  intro represented
  have location := represented (.stream 999) (by simp [untracked, ResourceState.set])
  cases location with
  | activeStream active =>
      dsimp only [replayed] at active
      rw [SharedOwnerFailure.work_shape] at active
      cbv at active
      cases active
  | bufferedStream found _stored held =>
      have absent
          : 999 ∉ replayed.queue.taskNodes.flatMap (fun node => node.childStreams) := by
        dsimp only [replayed]
        rw [SharedOwnerFailure.work_shape]
        cbv
        intro impossible
        cases impossible with
        | tail _ rest => cases rest
      exact absent (List.mem_flatMap.mpr
        ⟨_, (ReferenceWorkQueue.State.taskNode?_some found).1, held⟩)

example : ¬StopCoverage replayed untracked := by
  intro coverage
  have listed := coverage (.stream 999) (by simp [untracked, ResourceState.set])
  have absent : replayed.cleanupTargets.contains (.stream 999) = false := by
    dsimp only [replayed]
    rw [SharedOwnerFailure.work_shape]
    cbv
  have present : replayed.cleanupTargets.contains (.stream 999) = true := by simpa using listed
  rw [absent] at present
  contradiction

#print axioms GeneratedStopRootTopology_holds
#print axioms GeneratedRootedStopCoverage_holds
#print axioms GeneratedLiveContributorCoverage_holds
#print axioms GeneratedBufferedStopCoverage_holds
#print axioms covered
#print axioms coverage
#print axioms GeneratedRepresentedStopSafety_holds
#print axioms representation
#print axioms untracked_not_represented

end AlternativeStopCoverageChecks
