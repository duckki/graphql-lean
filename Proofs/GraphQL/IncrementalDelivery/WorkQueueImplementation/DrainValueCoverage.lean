import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValueRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PromotionPaths

/-! Recursive draining cannot lose a buffered value with a surviving contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every surviving live record was present before each bounded drain prefix
-----------------------------------------------------------------------------------------

/-- Startup only filters existing group records and retains their stored child edges. -/
theorem State.startNewWork_groupEdgesFrom (queue : State) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.GroupEdgesFrom queue := by
  have groupStep (current : State) (ref : NodeRef)
      : (current.startGroup ref available).1.GroupEdgesFrom current := by
    have cached : (current.cacheTaskFailures available).GroupEdgesFrom current := by
      intro key node found
      rw [State.groupNode?, State.cacheTaskFailures_groupNodes] at found
      exact ⟨node, found, rfl⟩
    unfold State.startGroup
    dsimp only
    split
    · exact cached
    · rename_i node found
      split
      · have unchanged (tasks : List Occurrence) (state : State)
            : (tasks.foldl (fun state task => state.startTask task available) state).groupNodes
              = state.groupNodes := by
          induction tasks generalizing state with
          | nil => rfl
          | cons task rest ih => rw [List.foldl_cons, ih, State.startTask_groupNodes]
        intro key node found
        rw [State.groupNode?, unchanged] at found
        exact cached key node found
      · exact ((current.cacheTaskFailures available).filterRefs_groupEdgesFrom (fun candidate =>
          !(State.removeGroup.collect ((current.cacheTaskFailures available).groupNodes.length + 1)
            (current.cacheTaskFailures available)
            [node.group.node.ref] []).contains candidate)).trans cached
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.GroupEdgesFrom queue)
      : (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.GroupEdgesFrom queue := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih => exact ih _ ((groupStep acc.1 ref).trans prior)
  have streams (refs : NodeRefs) (current : State) (prior : current.GroupEdgesFrom queue)
      : (refs.foldl State.startStream current).GroupEdgesFrom queue := by
    induction refs generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact prior
  unfold State.startNewWork
  exact streams _ _ (groups _ _ (fun key node found => ⟨node, found, rfl⟩))

/-- A bounded drain retains child-edge provenance through successful cleanup and startup.
No generated metadata or sufficient-budget premise is required.
-/
theorem State.drainReadyGroups_go_groupEdgesFrom (fuel : Nat) (queue : State)
    (available : List (Occurrence × Nat) := [])
    : (State.drainReadyGroups.go available fuel queue).1.GroupEdgesFrom queue := by
  induction fuel generalizing queue with
  | zero => exact .refl queue
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .refl queue
      · exact (ih _).trans ((State.startNewWork_groupEdgesFrom _ _ available).trans
          (queue.finishGroupSuccess_descendants _).1)

-----------------------------------------------------------------------------------------
-- One occurrence-labelled ledger covers successful flushes and failed cleanup together
-----------------------------------------------------------------------------------------

/-- Splitting a drain budget retains the exact intermediate queue and output order.
Witness: induction on the first budget; an exhausted ready set stays exhausted, while a
real closure contributes its output before both remaining segments. Thus a bounded drain
used below is an actual execution prefix, not a separately chosen trace.
-/
theorem State.drainReadyGroups_go_add (first rest : Nat) (queue : State)
    (available : List (Occurrence × Nat) := [])
    : State.drainReadyGroups.go available (first + rest) queue
      = let before := State.drainReadyGroups.go available first queue
        let after := State.drainReadyGroups.go available rest before.1
        (after.1, before.2.1 ++ after.2.1, before.2.2 ++ after.2.2) := by
  induction first generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ first ih =>
      simp only [Nat.succ_add, State.drainReadyGroups.go]
      split
      · rename_i stopped
        cases rest <;> simp only [State.drainReadyGroups.go, stopped, List.nil_append]
      · dsimp only; simp only [ih, List.append_assoc]

/-- Every stored value with a contributor still live after a drain prefix is published or
retained exactly. Witness: successful flushes extend the same publication inventory;
startup removal retains the task through its surviving owner. Available failures exclude
the buffered task itself, as required for exact record preservation. The endpoint owner
is an internal liveness condition, not a cancellation
certificate for tasks whose owners are all absent.
-/
theorem State.PublicationInventory.drainReadyGroups_go_conserves {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (fuel : Nat) (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          property occurrence value → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value _ errors member; cases member)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (State.drainReadyGroups.go available fuel queue).2.1.flatMap
              WorkQueueEvent.objectValues
        ∧ (State.drainReadyGroups.go available fuel queue).1.PublicationInventory property
            (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (∃ contributor ∈ node.task.groups,
                ∃ owner,
                  (State.drainReadyGroups.go available fuel queue).1.groupNode?
                    contributor.ref
                  = some owner)
            → (occurrence, value) ∈ added
              ∨ (State.drainReadyGroups.go available fuel queue).1.taskNode? occurrence
                = some node) := by
  induction fuel generalizing queue published with
  | zero =>
      exact ⟨
        [],
        rfl,
        by simpa only [State.drainReadyGroups.go, List.append_nil] using inventory,
        fun _ _ _ found _ _ => Or.inr found
      ⟩
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact ⟨[], rfl, by simpa using inventory, fun _ _ _ found _ _ => Or.inr found⟩
      · rename_i group selected
        obtain ⟨first, before, output, firstValues, flushed, conserved⟩ :=
          inventory.finishGroupSuccess_conserves group
        have activated := State.PublicationInventory.mk flushed.unique flushed.provenance
          (flushed.stored.startNewWork (queue.finishGroupSuccess group).2.2 available)
        obtain ⟨later, laterValues, final, laterConserved⟩ := ih activated
        refine ⟨first ++ later, ?_, ?_, ?_⟩
        · simp only [List.map_append, List.flatMap_append, output,
            List.flatMap_singleton, WorkQueueEvent.objectValues, List.append_nil,
            firstValues, laterValues]
        · simpa only [List.append_assoc] using final
        · intro occurrence node value found stored live
          rcases conserved occurrence node value found stored with earlier | retained
          · exact Or.inl (List.mem_append_left _ earlier)
          · obtain ⟨contributor, contributes, owner, finalOwner⟩ := live
            obtain ⟨survivor, survives, _⟩ :=
              State.drainReadyGroups_go_groupEdgesFrom fuel _ available _ _ finalOwner
            have own : ∀ errors, (occurrence, errors) ∉ available := by
              have source := (inventory.stored node (State.taskNode?_some found).1 value stored).1
              rw [(State.taskNode?_some found).2] at source
              exact clean occurrence value source
            have kept := State.startNewWork_lookup_existing retained _ available own contributes
              (List.mem_of_find?_eq_some survives) (State.groupNode?_ref survives)
            rcases laterConserved occurrence node value kept stored
                ⟨contributor, contributes, owner, finalOwner⟩ with now | still
            · exact Or.inl (List.mem_append_right _ now)
            · exact Or.inr still

/-- Full release-time draining retains or publishes every value with a surviving owner.
Witness: specialize bounded conservation to the implementation's live-node budget.
Startup failures and recursively promoted successes use one compatible publication ledger.
-/
theorem State.PublicationInventory.drainReadyGroups_conserves {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          property occurrence value → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value _ errors member; cases member)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.drainReadyGroups available).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (queue.drainReadyGroups available).1.PublicationInventory property
            (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (∃ contributor ∈ node.task.groups,
                ∃ owner,
                  (queue.drainReadyGroups available).1.groupNode? contributor.ref
                  = some owner)
            → (occurrence, value) ∈ added
              ∨ (queue.drainReadyGroups available).1.taskNode? occurrence = some node) :=
  inventory.drainReadyGroups_go_conserves queue.groupNodes.length available clean

-----------------------------------------------------------------------------------------
-- Values present before a mixed drain prefix are covered before a later live-owner close
-----------------------------------------------------------------------------------------

/-- A stored contributor publishes strictly before a later successful closure, even when
the preceding bounded drain also removes failed startup groups. Witness: the closing owner's
live lookup protects the value through that prefix; active membership then supplies the
final flush. Both stages extend one occurrence-labelled inventory. Replay must establish
the actual closing boundary and its active links; no absent-task cancellation is inferred.
-/
theorem State.PublicationInventory.drainPrefix_finishGroupSuccess_contributors
    {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (fuel : Nat) (group : GroupNode)
    (available : List (Occurrence × Nat) := [])
    (found
      : (State.drainReadyGroups.go available fuel queue).1.groupNode? group.group.node.ref
        = some group)
    (active
      : group.group.node.ref
        ∈ (State.drainReadyGroups.go available fuel queue).1.rootGroups)
    (links : (State.drainReadyGroups.go available fuel queue).1.ActiveTaskLinks)
    (clean
      : ∀ occurrence value,
          property occurrence value → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value _ errors member; cases member)
    : let drained := State.drainReadyGroups.go available fuel queue
      let closed := drained.1.finishGroupSuccess group
      ∃ (added : List ObjectPublication) (before : List WorkQueueEvent),
        drained.2.1 ++ closed.2.1
          = before
            ++ [.groupSuccess group.group.node closed.2.2.newGroups closed.2.2.newStreams]
        ∧ added.map Prod.snd = before.flatMap WorkQueueEvent.objectValues
        ∧ closed.1.PublicationInventory property (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → group.group.node.ref ∈ node.task.groups.map Execution.DeliveryNode.ref
            → (occurrence, value) ∈ added) := by
  dsimp only
  obtain ⟨first, firstValues, advanced, conserved⟩ :=
    inventory.drainReadyGroups_go_conserves fuel available clean
  obtain ⟨last, closeBefore, closeOutput, lastValues, final, covered⟩ :=
    advanced.finishGroupSuccess_contributors links group (List.mem_of_find?_eq_some found) active
  refine ⟨first ++ last,
    (State.drainReadyGroups.go available fuel queue).2.1 ++ closeBefore, ?_, ?_, ?_, ?_⟩
  · rw [closeOutput, List.append_assoc]
  · simp only [List.map_append, List.flatMap_append, firstValues, lastValues]
  · simpa only [List.append_assoc] using final
  · intro occurrence node value lookup stored contributes
    obtain ⟨contributor, member, same⟩ := List.mem_map.mp contributes
    have live : ∃ contributor ∈ node.task.groups, ∃ owner,
        (State.drainReadyGroups.go available fuel queue).1.groupNode? contributor.ref
          = some owner :=
      ⟨contributor, member, group, same.symm ▸ found⟩
    rcases conserved occurrence node value lookup stored live with earlier | retained
    · exact List.mem_append_left _ earlier
    · exact List.mem_append_right _
        (covered occurrence node value retained stored (List.mem_map.mpr ⟨_, member, same⟩))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
