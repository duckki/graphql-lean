import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StopRootTopology
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRequests
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay

/-! The actual fixed-snapshot cancelGroup walk reaches every rooted live group.
Distinct live visits fit its node-count budget; arbitrarily many stale links cost no fuel.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (NodeRefs Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (GroupNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- The finite frontier cannot repeat a live group or exhaust the real stop budget
-----------------------------------------------------------------------------------------

private theorem liveDescendant_key_le {queue : Kernel} {parents root target}
    (forest : queue.RemovalForest parents) (path : queue.LiveDescendant root target)
    : root ≤ target := by
  induction path with
  | self found => exact Nat.le_refl _
  | @child root node child target found linked below ih =>
      obtain ⟨next, nextFound⟩ := below.found
      have greater := forest.increasing (List.mem_of_find?_eq_some found)
        (List.mem_of_find?_eq_some nextFound)
        (ReferenceWorkQueue.State.groupNode?_ref nextFound ▸ linked)
      rw [ReferenceWorkQueue.State.groupNode?_ref found,
        ReferenceWorkQueue.State.groupNode?_ref nextFound] at greater
      exact Nat.le_trans (Nat.le_of_lt greater) ih

private structure StopFrontier (queue : Kernel) (parents : Nat → NodeRefs)
    (fuel : Nat) (pending visited : NodeRefs)
    : Prop where
  unique : (visited ++ pending).Nodup
  present : ∀ key ∈ visited, ∃ node, queue.groupNode? key = some node
  introduced
    : ∀ key ∈ visited ++ pending,
        key ∈ queue.rootGroups ∨ ∃ parent ∈ visited, (parents key).head? = some parent
  reachable
    : ∀ key ∈ visited ++ pending,
        (∃ node, queue.groupNode? key = some node)
        → ∃ root ∈ queue.rootGroups, queue.LiveDescendant root key
  budget : queue.groupNodes.length < fuel + visited.length

private theorem StopFrontier.fuel_pos {queue parents fuel pending visited}
    (frontier : StopFrontier queue parents fuel pending visited)
    : 0 < fuel := by
  have included : visited.Subset (queue.groupNodes.map (fun node => node.group.node.ref)) := by
    intro key member
    obtain ⟨node, found⟩ := frontier.present key member
    exact List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found,
      ReferenceWorkQueue.State.groupNode?_ref found⟩
  have bound := (List.nodup_append.mp frontier.unique).1.length_le_of_subset included
  simp only [List.length_map] at bound
  have budget := frontier.budget
  omega

private theorem StopFrontier.skip {queue parents fuel head rest visited}
    (frontier : StopFrontier queue parents fuel (head :: rest) visited)
    : StopFrontier queue parents fuel rest visited := by
  have subset : (visited ++ rest).Subset (visited ++ head :: rest) := by
    intro key member
    simp only [List.mem_append, List.mem_cons] at member ⊢
    exact member.imp_right Or.inr
  exact ⟨
    frontier.unique.sublist (by simp),
    frontier.present,
    fun key member => frontier.introduced key (subset member),
    fun key member => frontier.reachable key (subset member),
    frontier.budget
  ⟩

private theorem StopFrontier.visit {queue parents fuel head rest visited node}
    (forest : queue.RemovalForest parents) (antichain : queue.RootAntichain)
    (rootsPresent : queue.RootGroupsPresent)
    (frontier : StopFrontier queue parents (fuel + 1) (head :: rest) visited)
    (found : queue.groupNode? head = some node)
    : StopFrontier queue parents fuel (node.childGroups ++ rest) (head :: visited) := by
  have nodeMember := List.mem_of_find?_eq_some found
  have nodeKey := ReferenceWorkQueue.State.groupNode?_ref found
  obtain ⟨visitedUnique, pendingUnique, separate⟩ := List.nodup_append.mp frontier.unique
  have headAbsent : head ∉ visited := by
    intro member
    exact separate head member head (by simp) rfl
  have restAbsent := (List.nodup_cons.mp pendingUnique).1
  have childParent {child} (member : child ∈ node.childGroups)
      : (parents child).head? = some head := by
    simpa only [nodeKey] using forest.canonical node nodeMember child member
  have fresh {child} (member : child ∈ node.childGroups)
      : child ∉ visited ++ head :: rest := by
    intro old
    rcases frontier.introduced child old with root | ⟨parent, prior, parentEq⟩
    · have live : ∃ childNode, queue.groupNode? child = some childNode := by
        cases atChild : queue.groupNode? child with
        | none =>
            exact False.elim
              ((queue.groupNode?_eq_none_iff child).mp atChild (rootsPresent child root))
        | some childNode => exact ⟨childNode, rfl⟩
      obtain ⟨childNode, childFound⟩ := live
      obtain ⟨ancestor, active, path⟩ := frontier.reachable head (by simp) ⟨node, found⟩
      have same : ancestor = child := antichain ancestor active child root
        (path.trans (.child found member (.self childFound)))
      have lower := liveDescendant_key_le forest path
      have greater := forest.increasing nodeMember (List.mem_of_find?_eq_some childFound)
        (ReferenceWorkQueue.State.groupNode?_ref childFound ▸ member)
      rw [nodeKey, ReferenceWorkQueue.State.groupNode?_ref childFound] at greater
      rw [same] at lower
      exact Nat.not_lt_of_ge lower greater
    · have sameParent : parent = head := Option.some.inj
        (parentEq.symm.trans (childParent member))
      exact headAbsent (sameParent ▸ prior)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.cons_append, List.nodup_cons, List.nodup_append]
    refine ⟨?_, visitedUnique, ?_, ?_⟩
    · simp only [List.mem_append, not_or]
      exact ⟨headAbsent, fun child => fresh child (by simp), restAbsent⟩
    · refine ⟨forest.uniqueChildren node nodeMember, (List.nodup_cons.mp pendingUnique).2, ?_⟩
      intro child member key tail same
      subst key
      exact fresh member (by simp [tail])
    · intro key member child next same
      subst child
      rcases List.mem_append.mp next with child | tail
      · exact fresh child (by simp [member])
      · exact separate key member key (by simp [tail]) rfl
  · intro key member
    rcases List.mem_cons.mp member with same | prior
    · exact same ▸ ⟨node, found⟩
    · exact frontier.present key prior
  · intro key member
    simp only [List.cons_append, List.mem_cons, List.mem_append] at member
    rcases member with same | prior | child | tail
    · subst key
      exact (frontier.introduced head (by simp)).imp_right
        (fun ⟨parent, member, eq⟩ => ⟨parent, by simp [member], eq⟩)
    · exact (frontier.introduced key (by simp [prior])).imp_right
        (fun ⟨parent, member, eq⟩ => ⟨parent, by simp [member], eq⟩)
    · exact .inr ⟨head, by simp, childParent child⟩
    · exact (frontier.introduced key (by simp [tail])).imp_right
        (fun ⟨parent, member, eq⟩ => ⟨parent, by simp [member], eq⟩)
  · intro key member live
    simp only [List.cons_append, List.mem_cons, List.mem_append] at member
    rcases member with same | prior | child | tail
    · exact frontier.reachable key (by simp [same]) live
    · exact frontier.reachable key (by simp [prior]) live
    · obtain ⟨childNode, childFound⟩ := live
      obtain ⟨root, active, path⟩ := frontier.reachable head (by simp) ⟨node, found⟩
      exact ⟨root, active, path.trans (.child found child (.self childFound))⟩
    · exact frontier.reachable key (by simp [tail]) live
  · have budget := frontier.budget
    simp only [List.length_cons]
    omega

-----------------------------------------------------------------------------------------
-- Mirror the real task-before-child walk, without adding runtime visited bookkeeping
-----------------------------------------------------------------------------------------

private theorem cancelTasks_fold (state : State) (tasks : List Occurrence)
    (targets : List CleanupTarget)
    : tasks.foldl (fun targets occurrence => targets ++ state.cancelTask occurrence)
        targets
      = targets ++ tasks.flatMap state.cancelTask := by
  induction tasks generalizing targets with
  | nil => simp
  | cons task rest ih =>
      simp only [List.foldl_cons, ih, List.flatMap_cons, List.append_assoc]

private theorem StopFrontier.cancel_covers {state : State} {parents}
    (forest : state.queue.RemovalForest parents) (antichain : state.queue.RootAntichain)
    (rootsPresent : state.queue.RootGroupsPresent)
    (fuel : Nat) (pending visited : NodeRefs) (targets : List CleanupTarget)
    (frontier : StopFrontier state.queue parents fuel pending visited)
    : targets.Subset (state.cancelGroup fuel pending targets)
      ∧ ∀ key ∈ pending,
          ∀ target,
            state.queue.LiveDescendant key target
            → ∀ node,
                state.queue.groupNode? target = some node
                → (node.tasks.flatMap state.cancelTask).Subset
                    (state.cancelGroup fuel pending targets) := by
  induction fuel generalizing pending visited targets with
  | zero => exact False.elim (by have positive := frontier.fuel_pos; omega)
  | succ fuel ih =>
      induction pending generalizing visited targets with
      | nil =>
          simp only [State.cancelGroup]
          exact ⟨List.Subset.refl _, by intro key member; cases member⟩
      | cons head rest tailIH =>
          cases found : state.queue.groupNode? head with
          | none =>
              have next := tailIH visited targets frontier.skip
              simp only [State.cancelGroup, found]
              refine ⟨next.1, ?_⟩
              intro key member target path node atTarget
              rcases List.mem_cons.mp member with same | later
              · subst key
                obtain ⟨entry, present⟩ := path.found
                simp [found] at present
              · exact next.2 key later target path node atTarget
          | some node =>
              have next := ih (node.childGroups ++ rest) (head :: visited)
                (targets ++ node.tasks.flatMap state.cancelTask)
                (frontier.visit forest antichain rootsPresent found)
              simp only [State.cancelGroup, found, cancelTasks_fold]
              refine ⟨fun _ member => next.1 (List.mem_append_left _ member), ?_⟩
              intro key member target path entry atTarget
              rcases List.mem_cons.mp member with same | later
              · subst key
                cases path with
                | self present =>
                    have same := Option.some.inj (found.symm.trans atTarget)
                    subst entry
                    exact fun _ member => next.1 (List.mem_append_right _ member)
                | child present linked below =>
                    have same := Option.some.inj (found.symm.trans present)
                    subst node
                    exact next.2 _ (List.mem_append_left _ linked) target below entry atTarget
              · exact next.2 key (List.mem_append_right _ later) target path entry atTarget

/-- The actual stop budget reaches every task in every live group below an active root.
No bound on stale child keys is needed; only distinct live visits consume fuel.
-/
theorem State.rootedGroup_cancelTargets {state : State} {parents root target node}
    (forest : state.queue.RemovalForest parents) (unique : state.queue.rootGroups.Nodup)
    (antichain : state.queue.RootAntichain) (rootsPresent : state.queue.RootGroupsPresent)
    (active : root ∈ state.queue.rootGroups)
    (path : state.queue.LiveDescendant root target)
    (found : state.queue.groupNode? target = some node)
    : (node.tasks.flatMap state.cancelTask).Subset
        (state.cancelGroup (state.queue.groupNodes.length + 1) state.queue.rootGroups
          []) := by
  have frontier : StopFrontier state.queue parents (state.queue.groupNodes.length + 1)
      state.queue.rootGroups [] := {
    unique := unique
    present := by simp
    introduced := by intro key member; exact .inl member
    reachable := by intro key member ⟨entry, found⟩; exact ⟨key, member, .self found⟩
    budget := by simp
  }
  exact (frontier.cancel_covers forest antichain rootsPresent _ _ _ []).2
    root active target path node found

/-- A task-held source below a live rooted owner occurs in the actual deduplicated stop set.
Task membership and its held source are checked against the same fixed queue snapshot.
-/
theorem State.rootedTask_cleanupTargets {state : State}
    {parents root target group occurrence} (forest : state.queue.RemovalForest parents)
    (unique : state.queue.rootGroups.Nodup) (antichain : state.queue.RootAntichain)
    (rootsPresent : state.queue.RootGroupsPresent)
    (active : root ∈ state.queue.rootGroups)
    (path : state.queue.LiveDescendant root target)
    (found : state.queue.groupNode? target = some group)
    (linked : occurrence ∈ group.tasks)
    : (state.cancelTask occurrence).Subset state.cleanupTargets := by
  intro resource member
  apply (mem_uniqueCleanupTargets _ _).mpr
  apply List.mem_append_left
  exact State.rootedGroup_cancelTargets forest unique antichain rootsPresent active path found
    (List.mem_flatMap.mpr ⟨occurrence, linked, member⟩)

-----------------------------------------------------------------------------------------
-- Derive every structural stop premise from generated replay
-----------------------------------------------------------------------------------------

private theorem generatedStop_forest {work inputs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ∃ parents,
        ((State.initialize work).runNormalized inputs).1.queue.RemovalForest parents := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · refine ⟨fun _ => [], ?_, ?_, ?_⟩
    · intro node member; cases member
    · intro node member; cases member
    · intro node child member; cases member
  · obtain ⟨parents, canonical, links, records⟩ := generated.runNormalized_groupMetadata valid
    exact ⟨parents, ReferenceWorkQueue.State.RemovalForest.of_generated generated
      (ReferenceWorkQueue.createWorkQueue_runNormalized_childGroupsUnique _ _) links records
        canonical⟩

private theorem generatedStop_rootsPresent {work inputs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((State.initialize work).runNormalized inputs).1.queue.RootGroupsPresent := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · intro key member; cases member
  · exact generated.runNormalized_rootsPresent inputs (fun _ member => valid.eachMatches member)

/-- Generated replay's stop covers each task and held source at any rooted live owner.
Root reachability is deliberately explicit: this theorem does not infer acquisition or
prove that every native lease has such an owner. All traversal premises are constructed.
-/
def GeneratedRootedStopCoverage : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ∀ root target group occurrence,
        let state := ((State.initialize work).runNormalized inputs).1
        root ∈ state.queue.rootGroups
        → state.queue.LiveDescendant root target
        → state.queue.groupNode? target = some group
        → occurrence ∈ group.tasks
        → (state.cancelTask occurrence).Subset state.cleanupTargets

/-- The rooted-owner reduction uses the exact alternative state and actual stop traversal. -/
theorem GeneratedRootedStopCoverage_holds : GeneratedRootedStopCoverage := by
  intro work inputs generated valid started root target group occurrence
  dsimp only
  intro active path found linked
  obtain ⟨parents, forest⟩ := generatedStop_forest generated valid started
  obtain ⟨unique, antichain⟩ := GeneratedStopRootTopology_holds work inputs generated valid started
  exact State.rootedTask_cleanupTargets forest unique antichain
    (generatedStop_rootsPresent generated valid started) active path found linked

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
