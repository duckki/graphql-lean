import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementClosure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorRetirement

/-! Structural retirement and missing-parent certificates through matched source replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Bundle only independently established structural facts needed by actual handlers
-----------------------------------------------------------------------------------------

/-- Internal proof frame for group metadata, registration, and retirement structure.
No failure inventory, health assumption, output history, or scheduler premise is included.
-/
private structure RetirementFrame (queue : State) (work : Execution.Work)
    (parents : Nat → Keys)
    : Prop where
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  live : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  roots : queue.RootAncestorsRetired work
  retired : queue.UncancelledRetiredAncestors work

/-- Activation retains the frame when new roots have their ancestor certificates.
Witness: unchanged metadata and permanent retirements, plus the root-list extension law.
-/
private theorem RetirementFrame.startNewWork {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (released : NewWork)
    (protectedRoots : ∀ node ∈ released.newGroups, queue.AncestorsRetired work node.key)
    : RetirementFrame (queue.startNewWork released) work parents := by
  have registered := State.startNewWork_registration prior.live prior.tasks released
  exact ⟨prior.groups.startNewWork _, prior.links.startNewWork _,
    registered.1, registered.2, prior.roots.startNewWork _ protectedRoots,
    prior.retired.startNewWork _⟩

/-- The ready-group drain retains the complete structural frame.
Witness: joint root/retirement preservation and independent metadata/registry theorems.
-/
private theorem RetirementFrame.drainReadyGroups {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : RetirementFrame queue.drainReadyGroups.1 work parents := by
  have retired := queue.drainReadyGroups_uncancelledRetirement prior.retired generated
    prior.groups prior.links canonical prior.live prior.tasks prior.roots
  have registered := queue.drainReadyGroups_registration prior.live prior.tasks
  exact ⟨prior.groups.drainReadyGroups, prior.links.drainReadyGroups,
    registered.1, registered.2.1, retired.1, retired.2⟩

/-- Every drain notice retains its ancestor retirements through the remaining drain.
Witness: each successful closure protects its pruned frontier before activation; later
success or failure cleanup cannot recreate those ancestors. The child may later fail.
-/
private theorem RetirementFrame.drainReadyGroups_go_noticeRetirement
    {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.GroupNoticeAncestorsRetired work
        (State.drainReadyGroups.go fuel queue).2 := by
  have loop (fuel : Nat) (current : State) (frame : RetirementFrame current work parents)
      : (State.drainReadyGroups.go fuel current).1.GroupNoticeAncestorsRetired work
          (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current with
    | zero => exact .of_noNotices (by simp [State.drainReadyGroups.go])
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact .of_noNotices (by simp)
        · rename_i node selected
          obtain ⟨key, active, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : current.groupNode? key with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if candidate.failure.isSome || candidate.pending == 0 then
                some candidate else none) = some node at choice
              split at choice
              · cases Option.some.inj choice
                have member := List.mem_of_find?_eq_some found
                have roots := frame.roots _ (current.groupNode?_key found ▸ active)
                cases cached : node.failure with
                | none =>
                    have certificates := current.finishGroupSuccess_ancestorsRetired
                      generated frame.groups frame.links canonical frame.live member roots
                    have registered := current.finishGroupSuccess_registration
                      frame.live frame.tasks node
                    have next : RetirementFrame (current.finishGroupSuccess node).1
                        work parents :=
                      ⟨frame.groups.finishGroupSuccess _, frame.links.finishGroupSuccess _,
                        registered.1, registered.2.1,
                        frame.roots.mono (current.finishGroupSuccess_rootsSubset _)
                          (fun _ retired => retired.finishGroupSuccess _),
                        frame.retired.finishGroupSuccess generated frame.groups frame.links
                          canonical frame.live member roots⟩
                    have noticed := State.finishGroupSuccess_noticeAncestorRetirement
                      certificates.2.2
                    exact (noticed.mono (fun _ retired =>
                      (retired.startNewWork _).drainReadyGroups_go fuel)).append
                      (ih _ (next.startNewWork _ certificates.2.2))
                | some errors =>
                    have next : RetirementFrame (current.finishGroupFailure node errors).1
                        work parents :=
                      ⟨frame.groups.removeGroup _, frame.links.removeGroup _,
                        fun child included => frame.live child (List.mem_filter.mp included).1,
                        frame.tasks, frame.roots.mono (current.removeGroup_rootsSubset _)
                          (fun _ retired => retired.removeGroup _),
                        frame.retired.removeGroup _⟩
                    exact (State.GroupNoticeAncestorsRetired.of_noNotices (by
                      intro event emitted
                      simp only [State.finishGroupFailure, List.mem_singleton] at emitted
                      subst event
                      rfl)).append (ih _ next)
              · contradiction
  exact loop fuel queue prior

/-- The complete drain retains notice ancestry at its actual live-node budget.
Witness: specialize the bounded structural proof without extending the output history.
-/
private theorem RetirementFrame.drainReadyGroups_noticeRetirement
    {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    : queue.drainReadyGroups.1.GroupNoticeAncestorsRetired work
        queue.drainReadyGroups.2 :=
  prior.drainReadyGroups_go_noticeRetirement generated canonical queue.groupNodes.length

/-- Every bounded drain prefix certifies the retired ancestry of its own carried notices.
Witness: the local structural frame follows actual closures, retaining earlier notice
certificates through later cleanup. The budget can stop at an internal carrier boundary.
-/
theorem State.drainReadyGroups_go_noticeAncestorsRetired
    {queue : State} {work parents}
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (retired : queue.UncancelledRetiredAncestors work) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.GroupNoticeAncestorsRetired work
        (State.drainReadyGroups.go fuel queue).2 :=
  (show RetirementFrame queue work parents from ⟨
    records,
    links,
    live,
    tasks,
    roots,
    retired
  ⟩).drainReadyGroups_go_noticeRetirement
    generated canonical fuel

/-- Matched child integration retains old root certificates and structural retirement.
Witness: canonical record installation and unchanged roots; no child availability premise.
-/
private theorem RetirementFrame.maybeIntegrateWork {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (parentFields
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.key).head?)
    (covered
      : ∀ task ∈ newWork.tasks,
        ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
          ∃ group ∈ newWork.groups, group.node.key = key)
    (parentTask : Option Occurrence := none)
    : RetirementFrame (queue.maybeIntegrateWork newWork parentTask).1 work parents := by
  have registered := queue.maybeIntegrateWork_registration prior.live prior.tasks
    newWork covered parentTask
  exact ⟨
    prior.groups.maybeIntegrateWork newWork known parentTask,
    prior.links.maybeIntegrateWork newWork parentFields parentTask,
    registered.1,
    registered.2.1,
    prior.roots.mono
      (by rw [queue.maybeIntegrateWork_rootGroups]; exact fun _ member => member)
      (fun _ retired => retired.maybeIntegrateWork newWork parentTask),
    prior.retired.maybeIntegrateWork newWork parentTask
  ⟩

-----------------------------------------------------------------------------------------
-- Task success and failure keep the structural invariant independent of error accounting
-----------------------------------------------------------------------------------------

/-- Successful task handling preserves structural retirement and emitted notice ancestry.
Witness: matched child integration, protected successful closures, activation, and drain.
The ignored-success branch performs only membership cleanup.
-/
private theorem RetirementFrame.taskSuccess_with_notices {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : RetirementFrame (queue.taskSuccess occurrence result).1 work parents
      ∧ (queue.taskSuccess occurrence result).1.GroupNoticeAncestorsRetired work
          (queue.taskSuccess occurrence result).2 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskSuccess, found]
        using And.intro prior (State.GroupNoticeAncestorsRetired.of_noNotices (by simp))
  | some taskNode =>
      rw [queue.taskSuccess_eq occurrence result taskNode found]
      split
      · refine ⟨⟨prior.groups.removeTask _, prior.links.removeTask _, ?_, prior.tasks,
          prior.roots.mono (fun _ member => member)
            (fun _ retired => retired.removeTask occurrence), prior.retired.removeTask _⟩,
          .of_noNotices (by simp)⟩
        intro node member
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        exact prior.live old oldMember
      · let stored := queue.putTaskNode { taskNode with value := some result.value }
        have storedFrame : RetirementFrame stored work parents :=
          ⟨prior.groups, prior.links, prior.live, prior.tasks, prior.roots, prior.retired⟩
        have integrated := storedFrame.maybeIntegrateWork result.work
          (fun _ member => matching.taskChildGroups_recordAt member)
          (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
          matching.childTasksCovered (some occurrence)
        have folded := successGroupFold_uncancelledRetirement integrated.retired generated
          integrated.groups integrated.links canonical integrated.live integrated.tasks
          integrated.roots taskNode.task.groups
        have protectedRoots := successGroupFold_ancestorsRetired generated integrated.groups
          integrated.links canonical integrated.live integrated.tasks integrated.roots
          taskNode.task.groups
        let final := taskNode.task.groups.foldl successGroupStep
          ((stored.maybeIntegrateWork result.work (some occurrence)).1, [], {})
        have finalFrame : RetirementFrame final.1 work parents :=
          ⟨folded.1, folded.2.1, folded.2.2.1, folded.2.2.2.1,
            folded.2.2.2.2.1, folded.2.2.2.2.2⟩
        have activated := finalFrame.startNewWork final.2.2 protectedRoots.2
        have noticed := State.successGroupFold_noticeAncestorRetirement protectedRoots.2
        exact ⟨activated.drainReadyGroups generated canonical,
          (noticed.mono (fun _ retired => (retired.startNewWork _).drainReadyGroups)).append
            (activated.drainReadyGroups_noticeRetirement generated canonical)⟩

/-- Task failure preserves uncancelled retirement without proving any failure healthy.
Witness: cached failures leave live keys unchanged; removals mark every new retirement
cancelled. This covers the ignored-failure cleanup branch as well.
-/
theorem State.UncancelledRetiredAncestors.taskFailure {queue : State} {work}
    (prior : queue.UncancelledRetiredAncestors work) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.UncancelledRetiredAncestors work := by
  have step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (invariant : acc.1.UncancelledRetiredAncestors work)
      : (failureGroupStep errors acc group).1.UncancelledRetiredAncestors work := by
    obtain ⟨current, events⟩ := acc
    dsimp only [failureGroupStep]
    split
    · exact invariant
    · split
      · exact invariant.removeGroup _
      · exact invariant.putGroupNode _
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (invariant : acc.1.UncancelledRetiredAncestors work)
      : (groups.foldl (failureGroupStep errors) acc).1.UncancelledRetiredAncestors
          work := by
    induction groups generalizing acc with
    | nil => exact invariant
    | cons group rest ih => exact ih _ (step acc group invariant)
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using prior
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      split
      · exact prior.removeTask occurrence
      · exact loop node.task.groups _ (prior.removeTask occurrence)

-----------------------------------------------------------------------------------------
-- Streaming may prune taskless wrappers before activating their protected descendants
-----------------------------------------------------------------------------------------

/-- One matched stream item preserves structural retirement through real taskless pruning.
Witness: initially parentless candidates have empty ancestry; pruning transfers their
certificates to promoted descendants, whose ancestry need not be empty.
-/
private theorem RetirementFrame.integrateStreamItem_with_notices
    {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : RetirementFrame (queue.integrateStreamItem item) work parents
      ∧ ∀ child ∈
          ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
            (queue.maybeIntegrateWork item.work).2.newGroups).2,
          (queue.integrateStreamItem item).AncestorsRetired work child.key := by
  let integrated := queue.maybeIntegrateWork item.work
  have integratedFrame : RetirementFrame integrated.1 work parents :=
    prior.maybeIntegrateWork item.work
      (fun _ candidate => matching.streamItem_childGroups_recordAt member candidate)
      (fun _ candidate => matching.streamItem_childGroups_parentCanonical canonical
        member candidate) (matching.streamItem_childTasksCovered member)
  have protectedRoots : ∀ node ∈ integrated.2.newGroups,
      integrated.1.AncestorsRetired work node.key := by
    intro node included
    rw [State.maybeIntegrateWork_newGroups] at included
    obtain ⟨group, candidate, same, parentless, _⟩ :=
      queue.addGroups_newGroup_candidate item.work.groups included
    obtain ⟨dependencies, record⟩ := matching.streamItem_childGroups_recordAt member candidate
    have head := matching.streamItem_childGroups_parentCanonical canonical member candidate
    rw [parentless, ← canonical _ _ record] at head
    have empty : dependencies = [] := List.head?_eq_none_iff.mp head.symm
    rw [← same]
    exact .of_record generated record (by simp [empty])
  have prunedRoots := State.pruneEmptyGroups_ancestorsRetired generated integratedFrame.groups
    integratedFrame.links canonical integratedFrame.live integrated.2.newGroups protectedRoots
  have registered := State.pruneEmptyGroups_registration integratedFrame.live
    integratedFrame.tasks integrated.2.newGroups
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have prunedFrame : RetirementFrame pruned.1 work parents :=
    ⟨integratedFrame.groups.pruneEmptyGroups _, integratedFrame.links.pruneEmptyGroups _,
      registered.1, registered.2.1,
      integratedFrame.roots.mono
        (by rw [State.pruneEmptyGroups_rootGroups]; exact fun _ member => member)
        (fun _ retired => retired.pruneEmptyGroups _),
      integratedFrame.retired.pruneEmptyGroups generated integratedFrame.groups
        integratedFrame.links canonical integratedFrame.live _ protectedRoots⟩
  exact ⟨prunedFrame.startNewWork { integrated.2 with newGroups := pruned.2 } prunedRoots,
    fun child member => (prunedRoots child member).mono
      (fun _ retired => retired.startNewWork _)⟩

/-- Sequential item integration retains structural retirement before any drain output.
Witness: induction over the actual integration fold with each item's matching evidence.
-/
private theorem RetirementFrame.streamItemFold_with_notices {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : let prepared := items.foldl streamItemStep (queue, [], [], [])
      RetirementFrame prepared.1 work parents
      ∧ ∀ child ∈ prepared.2.1, prepared.1.AncestorsRetired work child.key := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (invariant : RetirementFrame acc.1 work parents)
      (protectedRoots : ∀ child ∈ acc.2.1, acc.1.AncestorsRetired work child.key)
      : RetirementFrame (more.foldl streamItemStep acc).1 work parents
        ∧ ∀ child ∈ (more.foldl streamItemStep acc).2.1,
          (more.foldl streamItemStep acc).1.AncestorsRetired work child.key := by
    induction more generalizing acc with
    | nil => exact ⟨invariant, protectedRoots⟩
    | cons item rest ih =>
        have integrated := invariant.integrateStreamItem_with_notices generated canonical
          matching (included List.mem_cons_self)
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) _ integrated.1
        intro child member
        rcases List.mem_append.mp member with old | new
        · exact (protectedRoots child old).mono (fun _ retired =>
            ((retired.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
        · exact integrated.2 child new
  exact loop items (fun _ member => member) (queue, [], [], []) prior (by simp)

/-- Item handling retains notice ancestry through preparation and its subsequent drain.
Witness: combine the exact preparation frontier with the independent drain theorem,
transporting earlier ancestor retirements through later successful or failing cleanup.
-/
private theorem RetirementFrame.streamItems_with_notices {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : RetirementFrame (queue.streamItems stream items).1 work parents
      ∧ (queue.streamItems stream items).1.GroupNoticeAncestorsRetired work
          (queue.streamItems stream items).2 := by
  rw [queue.streamItems_eq stream items]
  split
  · exact ⟨prior, .of_noNotices (by simp)⟩
  · have folded := prior.streamItemFold_with_notices generated canonical matching
    refine ⟨folded.1.drainReadyGroups generated canonical, ?_⟩
    let final := items.foldl streamItemStep (queue, [], [], [])
    change final.1.drainReadyGroups.1.GroupNoticeAncestorsRetired work
      ([.streamValues stream final.2.2.2 final.2.1 final.2.2.1]
        ++ final.1.drainReadyGroups.2)
    apply State.GroupNoticeAncestorsRetired.append
    · intro key member
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, rawGroupNoticeKeys]
        at member
      obtain ⟨child, noticed, same⟩ := List.mem_map.mp member
      exact same ▸ (folded.2 child noticed).mono (fun _ retired => retired.drainReadyGroups)
    · exact folded.1.drainReadyGroups_noticeRetirement generated canonical

-----------------------------------------------------------------------------------------
-- Compose all actual input handlers and publisher-normalized host batches
-----------------------------------------------------------------------------------------

/-- Every matched event preserves the structural retirement frame.
Witness: success/item certificates and cancellation-marked failure removal; stream closure
does not modify group structure. Source timing and acceptance are not assumptions.
-/
private theorem RetirementFrame.handleGraphEvent {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : RetirementFrame (queue.handleGraphEvent event).1 work parents := by
  cases event with
  | taskSuccess occurrence result =>
      exact (prior.taskSuccess_with_notices generated canonical matching).1
  | taskFailure occurrence errors =>
      have registered := queue.taskFailure_registration prior.live prior.tasks occurrence errors
      exact ⟨prior.groups.taskFailure occurrence errors, prior.links.taskFailure occurrence errors,
        registered.1, registered.2.1,
        prior.roots.mono (queue.taskFailure_rootsSubset occurrence errors)
          (fun _ retired => retired.taskFailure occurrence errors),
        prior.retired.taskFailure occurrence errors⟩
  | streamItems stream items =>
      exact (prior.streamItems_with_notices generated canonical matching).1
  | streamSuccess stream =>
      change RetirementFrame (queue.streamSuccess stream).1 work parents
      unfold State.streamSuccess
      split
      all_goals
        exact ⟨prior.groups, prior.links, prior.live, prior.tasks, prior.roots, prior.retired⟩
  | streamFailure stream errors =>
      change RetirementFrame (queue.streamFailure stream errors).1 work parents
      unfold State.streamFailure
      split
      all_goals
        exact ⟨prior.groups, prior.links, prior.live, prior.tasks, prior.roots, prior.retired⟩

/-- Every actual handler retains the retired ancestry of its carried group notices.
Witness: the two notice-producing handlers supply certificates; the other handlers have
empty group-notice projections, independently of successful or failing payloads.
-/
private theorem RetirementFrame.handleGraphEvent_noticeRetirement
    {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.GroupNoticeAncestorsRetired work
        (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess occurrence result =>
      exact (prior.taskSuccess_with_notices generated canonical matching).2
  | streamItems stream items =>
      exact (prior.streamItems_with_notices generated canonical matching).2
  | taskFailure occurrence errors =>
      apply State.GroupNoticeAncestorsRetired.of_noNotices
      intro output member
      cases output with
      | groupSuccess group groups streams =>
          exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups
            streams member)
      | streamValues stream values groups streams =>
          have impossible : stream.key ∈
              (queue.taskFailure occurrence errors).2.flatMap rawStreamReferenceKeys :=
            List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩
          rw [State.taskFailure_streamReferences] at impossible
          cases impossible
      | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination
        =>
          rfl
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [State.GroupNoticeAncestorsRetired, rawGroupNoticeKeys]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [State.GroupNoticeAncestorsRetired, rawGroupNoticeKeys]

/-- A matched host batch retains the frame at each concrete handler state.
Witness: event-fold induction, followed only by an optional termination-flag update.
-/
private theorem RetirementFrame.handleGraphEvents {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : RetirementFrame (queue.handleGraphEvents events).1 work parents := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have loop (more : List GraphEvent) (included : more.Subset events)
      (acc : State × List WorkQueueEvent) (invariant : RetirementFrame acc.1 work parents)
      : RetirementFrame (more.foldl step acc).1 work parents := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons event rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (invariant.handleGraphEvent generated canonical event
            (matching event (included List.mem_cons_self)))
  unfold State.handleGraphEvents
  split
  · exact prior
  · have final := loop events (fun _ member => member) (queue, []) prior
    dsimp only
    split <;> exact ⟨final.groups, final.links, final.live, final.tasks, final.roots, final.retired⟩

/-- Publisher normalization preserves the queue's structural frame across matched batches.
Witness: the publisher leaves queue fields unchanged after each actual host-batch handler.
-/
private theorem RetirementFrame.runNormalized {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : RetirementFrame (queue.runNormalized batches).1 work parents := by
  have step (acc : NormalizedAcc) (batch : List GraphEvent)
      (matched : ∀ event ∈ batch, event.MatchesWork work)
      (invariant : RetirementFrame acc.1 work parents)
      : RetirementFrame (normalizedStep acc batch).1 work parents := by
    have next := invariant.handleGraphEvents generated canonical batch matched
    unfold normalizedStep
    dsimp only
    split <;> exact next
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (acc : NormalizedAcc) (invariant : RetirementFrame acc.1 work parents)
      : RetirementFrame (more.foldl normalizedStep acc).1 work parents := by
    induction more generalizing acc with
    | nil => exact invariant
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (step acc batch (matching batch (included List.mem_cons_self)) invariant)
  exact loop batches (fun _ member => member)
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, []) prior

/-- Sequential source replay preserves the same structural frame without batch controls.
Witness: fold over matched actual event handlers; termination flags are irrelevant here.
-/
private theorem RetirementFrame.replayGraphEvents {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : RetirementFrame (queue.replayGraphEvents events) work parents := by
  induction events generalizing queue with
  | nil => exact prior
  | cons event rest ih =>
      exact ih (prior.handleGraphEvent generated canonical event
        (matching event List.mem_cons_self))
        (fun next member => matching next (List.mem_cons_of_mem _ member))

-----------------------------------------------------------------------------------------
-- Generated replay has structural retirement without health or output-admission premises
-----------------------------------------------------------------------------------------

/-- Every matched generated-work replay preserves roots and uncancelled ancestor closure.
Witness: generated initialization and the structural handler induction, with no assumed
failure-health, pending-owner availability, start discipline, or output history.
-/
theorem ExecutedWork.runNormalized_structuralRetirement {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      queue.RootAncestorsRetired work ∧ queue.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have final := initial.runNormalized generated canonical batches matching
  exact ⟨final.roots, final.retired⟩

/-- Sequential matched replay retains root and uncancelled ancestor certificates.
Witness: generated initialization and the same structural handler induction, without
requiring accepted input, completed output, or a selected schedule.
-/
theorem ExecutedWork.replayGraphEvents_structuralRetirement {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      queue.RootAncestorsRetired work ∧ queue.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have final := initial.replayGraphEvents generated canonical events matching
  exact ⟨final.roots, final.retired⟩

/-- Actual carried notices have their task-bearing ancestors retired by that handler.
Witness: matched generated replay establishes the independent structural frame, and
notice-producing handlers retain certificates even for children later removed by a drain.
No source-validity, acceptance, failure-health, or output-admission premise is assumed.
-/
theorem ExecutedWork.replayGraphEvents_next_noticeAncestorsRetired
    {work before event} (generated : ExecutedWork work)
    (matching : ∀ past ∈ before, past.MatchesWork work)
    (incoming : event.MatchesWork work)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        (before ++ [event])).GroupNoticeAncestorsRetired
        work
        (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
          event).2 := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have prior := initial.replayGraphEvents generated canonical before matching
  simpa only [State.replayGraphEvents, List.foldl_append, List.foldl_cons, List.foldl_nil]
    using prior.handleGraphEvent_noticeRetirement generated canonical event incoming

/-- A matched successful input's prepared state has all structural release certificates.
Witness: the same generated replay frame, followed only by value installation and matched
child integration. No buffered-value, failure-health, or publication premise is needed.
-/
theorem ExecutedWork.replayGraphEvents_preparedRetirement {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work) {occurrence result}
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (node : TaskNode)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      let prepared :=
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      ∃ parents,
        (∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.key)
        ∧ prepared.GroupNodesMatchWork work
        ∧ prepared.ChildLinksCanonical parents
        ∧ prepared.LiveGroupsRegistered
        ∧ prepared.TaskGroupsRegistered
        ∧ prepared.RootAncestorsRetired work
        ∧ prepared.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have prior := initial.replayGraphEvents generated canonical events matching
  have stored : RetirementFrame
      (((State.initialize (Work.fromExecution work)).replayGraphEvents events).putTaskNode
        { node with value := some result.value }) work parents :=
    ⟨prior.groups, prior.links, prior.live, prior.tasks, prior.roots, prior.retired⟩
  have prepared := stored.maybeIntegrateWork result.work
    (fun _ member => matched.taskChildGroups_recordAt member)
    (fun _ member => matched.taskChildGroups_parentCanonical canonical member)
    matched.childTasksCovered (some occurrence)
  exact ⟨parents, canonical, prepared.groups, prepared.links, prepared.live, prepared.tasks,
    prepared.roots, prepared.retired⟩

/-- Matched stream-item preparation has the full structural frame before its ready drain.
Witness: generated replay establishes the frame; each actual item integration preserves
it through child registration, taskless-wrapper pruning, and root activation.
-/
theorem ExecutedWork.replayGraphEvents_streamPreparedRetirement {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work) {stream items}
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      let prepared := queue.preparedStreamItems items
      ∃ parents,
        (∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.key)
        ∧ prepared.GroupNodesMatchWork work
        ∧ prepared.ChildLinksCanonical parents
        ∧ prepared.LiveGroupsRegistered
        ∧ prepared.TaskGroupsRegistered
        ∧ prepared.RootAncestorsRetired work
        ∧ prepared.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have prior := initial.replayGraphEvents generated canonical events matching
  have prepared := State.preparedStreamItems_preserves
    (fun current => RetirementFrame current work parents) prior items
    (fun _ _ member frame =>
      (frame.integrateStreamItem_with_notices generated canonical matched member).1)
  exact ⟨parents, canonical, prepared.groups, prepared.links, prepared.live, prepared.tasks,
    prepared.roots, prepared.retired⟩

/-- A leading item carrier's noticed groups have retired ancestry before draining begins.
Witness: matched replay supplies the structural frame and the exact integration fold
protects its accumulated pruned frontier. No later drain closure is used as evidence.
-/
theorem ExecutedWork.streamItems_prepared_noticeAncestorsRetired
    {work before stream items} (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared := items.foldl streamItemStep (queue, [], [], [])
      ∀ child ∈ prepared.2.1, prepared.1.AncestorsRetired work child.key := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have prior := initial.replayGraphEvents generated canonical before matching
  exact (prior.streamItemFold_with_notices generated canonical matched).2

/-- Valid sequential replay has healthy-retirement closure for accepted object failures.
Witness: structural uncancelled closure and independently proved cancellation provenance.
No missing-parent health or contributor-availability premise is used.
-/
theorem ExecutedWork.replayGraphEvents_healthyRetiredAncestors {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).HealthyRetiredAncestors
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          events) :=
  (generated.replayGraphEvents_structuralRetirement events
    (fun _ member => valid.eachMatches member)).2.healthy
    (generated.replayGraphEvents_cancelledRecordsSupported events valid)

/-- Started normalized replay has healthy-retirement closure for its accepted failures.
Witness: structural replay closure and the accepted-inventory cancellation theorem.
Batch normalization is related to sequential failure inventory only by start discipline.
-/
theorem ExecutedWork.runNormalized_healthyRetiredAncestors {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.HealthyRetiredAncestors
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten) :=
  (generated.runNormalized_structuralRetirement batches
    (fun _ batch _ event =>
      valid.eachMatches (List.mem_flatten.mpr ⟨_, batch, event⟩))).2.healthy
    (generated.runNormalized_cancelledRecordsSupported batches valid started)

/-- Every valid generated replay supplies the structural missing-parent certificate.
Witness: the proved uncancelled retirement invariant, permanent parent registration,
and exact generated parent chains. This discharges structural retirement, not health
under the accepted-failure inventory, which still needs its separate accounting induction.
-/
theorem ExecutedWork.runNormalized_missingParentAncestorsRetired {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.MissingParentAncestorsRetired
        work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work :=
    fun _ batch _ event => valid.eachMatches (List.mem_flatten.mpr ⟨_, batch, event⟩)
  have closure := (generated.runNormalized_structuralRetirement batches matching).2
  have parentFields := (createWorkQueue_groupParentsCanonical (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
    ).runNormalized batches matching canonical
  exact closure.missingParent generated valid.runNormalized_groupNodesMatchWork parentFields
    canonical (generated.runNormalized_parentsRegistered valid)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
