import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalBookkeeping
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants

/-! Exact accounting projection of the real shrinking removal walk.
The reference's finite-forest frontier proves that no visited key is revisited, so static
collection and dynamic deletion have the same reverse-preorder cancelled-key list. This
module intentionally erases task-node storage; full record correspondence is separate.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs)

private theorem filterTrue (items : List α) : items.filter (fun _ => true) = items :=
  List.filter_eq_self.mpr (fun _ _ => rfl)

-----------------------------------------------------------------------------------------
-- Accounting endpoint of a visited-key prefix
-----------------------------------------------------------------------------------------

/-- Reference accounting with the visited groups and active roots removed. -/
def removalAccountingCore (queue : ReferenceWorkQueue.State) (removed : NodeRefs)
    : ReferenceWorkQueue.State :=
  {
    registrationCore queue with
      groupNodes :=
        queue.groupNodes.filter (fun node => !removed.contains node.group.node.ref)
      rootGroups := queue.rootGroups.filter (fun key => !removed.contains key)
  }

private theorem removalAccountingCore_core (queue : ReferenceWorkQueue.State)
    (removed : NodeRefs)
    : removalAccountingCore (registrationCore queue) removed
      = removalAccountingCore queue removed :=
  rfl

private theorem eraseRemovalGroup_core (state : State) (key : Nat)
    : registrationCore (eraseRemovalGroup state key).queue
      = removalAccountingCore state.queue [key] := by
  simp only [registrationCore, eraseRemovalGroup, removalAccountingCore,
    List.contains_cons, List.contains_nil, Bool.or_false, bne]

private theorem removalAccountingCore_cons (queue : ReferenceWorkQueue.State)
    (removed : NodeRefs) (key : Nat)
    : removalAccountingCore (removalAccountingCore queue removed) [key]
      = removalAccountingCore queue (key :: removed) := by
  simp only [removalAccountingCore, registrationCore, List.filter_filter,
    List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_or]

private theorem accounting_lookup {queue : ReferenceWorkQueue.State} {state : State}
    {removed : NodeRefs}
    (core : registrationCore state.queue = removalAccountingCore queue removed)
    {key : Nat} (fresh : key ∉ removed)
    : state.queue.groupNode? key = queue.groupNode? key := by
  have groups := congrArg ReferenceWorkQueue.State.groupNodes core
  change state.queue.groupNodes = queue.groupNodes.filter
    (fun node => !removed.contains node.group.node.ref) at groups
  change state.queue.groupNodes.find? (fun node => node.group.node.ref == key) = _
  rw [groups, ReferenceWorkQueue.State.groupNode?_filterRefs queue
    (fun candidate => !removed.contains candidate) key]
  simp [fresh]

-----------------------------------------------------------------------------------------
-- Static reference collection and shrinking actual removal agree exactly
-----------------------------------------------------------------------------------------

/-- The actual walker keeps the same accounting core and reverse-preorder keys as the
reference collector. All endpoints come from the actual task fold; its group-store identity
uses existing structural matching and soundness, not a desired-state hypothesis.
-/
theorem removeGroup_walk_accounting {queue : ReferenceWorkQueue.State} {work : Work}
    {parents : Nat → NodeRefs} {root : Nat} (forest : queue.RemovalForest parents)
    (fuel : Nat) (pending removed : NodeRefs)
    (frontier
      : ReferenceWorkQueue.RemovalFrontier queue parents root fuel pending removed)
    (state : State) (targets : List CleanupTarget)
    (matching : state.queue.RegisteredTasksMatch work)
    (sound : state.queue.GroupMembershipSound)
    (core : registrationCore state.queue = removalAccountingCore queue removed)
    : let final := State.removeGroup.walk fuel state pending removed targets
      final.2.1 = ReferenceWorkQueue.State.removeGroup.collect fuel queue pending removed
      ∧ registrationCore final.1.queue = removalAccountingCore queue final.2.1
      ∧ final.1.queue.RegisteredTasksMatch work
      ∧ final.1.queue.GroupMembershipSound := by
  induction fuel generalizing pending removed state targets with
  | zero =>
      simp only [State.removeGroup.walk, ReferenceWorkQueue.State.removeGroup.collect]
      exact ⟨trivial, core, matching, sound⟩
  | succ fuel ih =>
      induction pending generalizing removed state targets with
      | nil =>
          simp only [State.removeGroup.walk, ReferenceWorkQueue.State.removeGroup.collect]
          exact ⟨trivial, core, matching, sound⟩
      | cons key rest tailIH =>
          have fresh : key ∉ removed := by
            obtain ⟨_, _, separate⟩ := List.nodup_append.mp frontier.unique
            intro member
            exact separate key member key (by simp) rfl
          have lookup := accounting_lookup core fresh
          cases found : queue.groupNode? key with
          | none =>
              simpa only [State.removeGroup.walk, ReferenceWorkQueue.State.removeGroup.collect,
                lookup, found] using tailIH removed frontier.skip state targets matching sound core
          | some group =>
              rw [State.removeGroup.walk, lookup, found,
                ReferenceWorkQueue.State.removeGroup.collect, found]
              let folded := group.tasks.foldl fusedRemovalTaskStep
                (eraseRemovalGroup state key, targets)
              have erasedMatch := eraseRemovalGroup_registeredTasksMatch matching key
              have erasedSound := eraseRemovalGroup_groupMembershipSound sound key
              have book := fusedRemovalTaskFold_bookkeeping group.tasks
                (eraseRemovalGroup state key, targets) erasedMatch erasedSound
              have nextCore : registrationCore folded.1.queue
                  = removalAccountingCore queue (key :: removed) := by
                rw [fusedRemovalTaskFold_registrationCore group.tasks
                    (eraseRemovalGroup state key, targets) erasedMatch erasedSound,
                  eraseRemovalGroup_core, ← removalAccountingCore_core state.queue [key], core,
                  removalAccountingCore_cons]
              exact ih (group.childGroups ++ rest) (key :: removed)
                (frontier.visit forest found) folded.1 folded.2 book.2.1 book.2.2 nextCore

/-- Root-level accounting projection target. These are reusable reference bookkeeping
premises, to be derived at generated handler points before lifting to public replay.
This is not full queue equality and does not assert native acquisition completeness.
-/
def FusedRemovalAccounting : Prop :=
  ∀ (state : State) (work : Work) (parents : Nat → NodeRefs) (root : Nat)
    (targets : List CleanupTarget),
    state.queue.RegisteredTasksMatch work
    → state.queue.GroupMembershipSound
    → state.queue.RemovalForest parents
    → registrationCore (state.removeGroup root targets).1.queue
      = registrationCore (state.queue.removeGroup root)

theorem FusedRemovalAccounting_holds : FusedRemovalAccounting := by
  intro state work parents root targets matching sound forest
  cases found : state.queue.groupNode? root with
  | none =>
      simp only [State.removeGroup, State.removeGroup.walk, found,
        ReferenceWorkQueue.State.removeGroup, ReferenceWorkQueue.State.removeGroup.collect,
        List.append_nil, List.contains_nil, Bool.not_false, filterTrue, registrationCore]
  | some group =>
      have frontier : ReferenceWorkQueue.RemovalFrontier state.queue parents root
          (state.queue.groupNodes.length + 1) [root] [] := {
        rootPresent := ⟨group, found⟩
        unique := by simp
        present := by simp
        introduced := by intro key member; exact Or.inl (by simpa using member)
        lower := by intro key member _; simp_all
        budget := by simp
      }
      have core : registrationCore state.queue = removalAccountingCore state.queue [] := by
        simp only [removalAccountingCore, List.contains_nil, Bool.not_false, filterTrue,
          registrationCore]
      have result := removeGroup_walk_accounting forest _ [root] [] frontier
        state targets matching sound core
      unfold State.removeGroup ReferenceWorkQueue.State.removeGroup
      simp only
      rw [← result.1]
      exact congrArg (fun current : ReferenceWorkQueue.State =>
        { current with cancelledGroups := current.cancelledGroups ++
          (State.removeGroup.walk (state.queue.groupNodes.length + 1)
            state [root] [] targets).2.1 }) result.2.1

/-- Generated reference prefixes supply all accounting premises independently. This is
the local transition bridge's domain construction; replay composition is proved separately.
-/
def GeneratedReferenceRemovalAccounting : Prop :=
  ∀ (work : Work) (batches : List (List GraphEvent)),
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work batches.flatten
    → ∀ (root : Nat) (targets : List CleanupTarget),
        let queue :=
          ((ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
            batches).1
        registrationCore (({ queue } : State).removeGroup root targets).1.queue
        = registrationCore (queue.removeGroup root)

/-- No host bookkeeping assumption is added: matching, soundness and the finite forest
are derived from execution work and the original valid-source prefix.
-/
theorem GeneratedReferenceRemovalAccounting_holds
    : GeneratedReferenceRemovalAccounting := by
  intro work batches generated valid root targets
  obtain ⟨parents, forest⟩ := generated.runNormalized_removalForest batches valid
  exact FusedRemovalAccounting_holds _ work parents root targets
    (ReferenceWorkQueue.createWorkQueue_runNormalized_registeredTasksMatch valid)
    (ReferenceWorkQueue.createWorkQueue_runNormalized_groupMembershipSound
      (ReferenceWorkQueue.Work.fromExecution work) batches) forest

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
