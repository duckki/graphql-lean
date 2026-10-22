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
    (parents : Nat → NodeRefs)
    : Prop where
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  live : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  roots : queue.RootAncestorsRetired work
  retired : queue.UncancelledRetiredAncestors work

/-- Cache exposure changes no structural retirement data. -/
private theorem RetirementFrame.cacheTaskFailures {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (available : List (Occurrence × Nat))
    : RetirementFrame (queue.cacheTaskFailures available) work parents := by
  have covered := queue.cacheTaskFailures_registration prior.live prior.tasks available
  refine ⟨prior.groups.cacheTaskFailures available, prior.links.cacheTaskFailures available,
    covered.1, covered.2, ?_, prior.retired.cacheTaskFailures available⟩
  intro ref active
  rw [State.cacheTaskFailures_rootGroups] at active
  exact (prior.roots ref active).mono (fun _ retired => retired.cacheTaskFailures available)

/-- Activation retains the frame when new roots have their ancestor certificates.
Witness: unchanged metadata and permanent retirements, plus the root-list extension law.
-/
private theorem RetirementFrame.startNewWork {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (released : NewWork)
    (protectedRoots : ∀ node ∈ released.newGroups, queue.AncestorsRetired work node.ref)
    (available : List (Occurrence × Nat) := [])
    : RetirementFrame (queue.startNewWork released available).1 work parents := by
  have registered := State.startNewWork_registration prior.live prior.tasks released available
  exact ⟨prior.groups.startNewWork _ available, prior.links.startNewWork _ available,
    registered.1, registered.2, prior.roots.startNewWork _ protectedRoots available,
    prior.retired.startNewWork _ available⟩

/-- The ready-group drain retains the complete structural frame.
Witness: joint root/retirement preservation and independent metadata/registry theorems.
-/
private theorem RetirementFrame.drainReadyGroups {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : RetirementFrame (queue.drainReadyGroups available).1 work parents := by
  have retired := queue.drainReadyGroups_uncancelledRetirement prior.retired generated
    prior.groups prior.links canonical prior.live prior.tasks prior.roots available
  have registered := queue.drainReadyGroups_registration prior.live prior.tasks available
  exact ⟨prior.groups.drainReadyGroups available, prior.links.drainReadyGroups available,
    registered.1, registered.2.1, retired.1, retired.2⟩

/-- Task rejection preserves the structural frame through retained computation replay. -/
private theorem RetirementFrame.taskFailure {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (occurrence : Occurrence) (errors : Nat)
    : RetirementFrame (queue.taskFailure occurrence errors).1 work parents := by
  have registered := queue.taskFailure_registration prior.live prior.tasks occurrence errors
  exact ⟨prior.groups.taskFailure occurrence errors, prior.links.taskFailure occurrence errors,
    registered.1, registered.2.1,
    prior.roots.mono (queue.taskFailure_rootsSubset occurrence errors)
      (fun _ retired => retired.taskFailure occurrence errors),
    prior.retired.taskFailure occurrence errors⟩

/-- Every drain notice retains its ancestor retirements through the remaining drain.
Witness: each successful closure protects its pruned frontier before activation; later
success or failure cleanup cannot recreate those ancestors. The child may later fail.
-/
private theorem RetirementFrame.drainReadyGroups_go_noticeRetirement
    {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (fuel : Nat)
    (available : List (Occurrence × Nat) := [])
    : (State.drainReadyGroups.go available fuel queue).1.GroupNoticeAncestorsRetired work
        (State.drainReadyGroups.go available fuel queue).2.1 := by
  have loop (fuel : Nat) (current : State) (frame : RetirementFrame current work parents)
      : (State.drainReadyGroups.go available fuel current).1.GroupNoticeAncestorsRetired work
          (State.drainReadyGroups.go available fuel current).2.1 := by
    induction fuel generalizing current with
    | zero => exact .of_noNotices (by simp [State.drainReadyGroups.go])
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact .of_noNotices (by simp)
        · rename_i node selected
          obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : current.groupNode? ref with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if candidate.pending == 0 then
                some candidate else none) = some node at choice
              split at choice
              · cases Option.some.inj choice
                have member := List.mem_of_find?_eq_some found
                have roots := frame.roots _ (current.groupNode?_ref found ▸ active)
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
                  (retired.startNewWork _ available).drainReadyGroups_go fuel available)).append
                  (ih _ (next.startNewWork _ certificates.2.2 available))
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
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.GroupNoticeAncestorsRetired work
        (queue.drainReadyGroups available).2.1 :=
  prior.drainReadyGroups_go_noticeRetirement generated canonical queue.groupNodes.length
    available

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
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (retired : queue.UncancelledRetiredAncestors work) (fuel : Nat)
    (available : List (Occurrence × Nat) := [])
    : (State.drainReadyGroups.go available fuel queue).1.GroupNoticeAncestorsRetired work
        (State.drainReadyGroups.go available fuel queue).2.1 :=
  (show RetirementFrame queue work parents from ⟨
    records,
    links,
    live,
    tasks,
    roots,
    retired
  ⟩).drainReadyGroups_go_noticeRetirement
    generated canonical fuel available

/-- Matched child integration retains old root certificates and structural retirement.
Witness: canonical record installation and unchanged roots; no child availability premise.
-/
private theorem RetirementFrame.maybeIntegrateWork {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (parentFields
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (covered
      : ∀ task ∈ newWork.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ref ∈ queue.registeredGroups ∨ ∃ group ∈ newWork.groups, group.node.ref = ref)
    (parentTask : Option Occurrence := none)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (closed
      : ∀ group ∈ newWork.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ newWork.groups.map (fun group => group.node.ref))
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
    prior.retired.maybeIntegrateWork newWork parentTask generated prior.live
      (by
        intro group member
        obtain ⟨dependencies, record⟩ := known group member
        exact ⟨
          dependencies,
          record,
          by rw [canonical _ _ record]; exact parentFields group member
        ⟩)
      closed
  ⟩

-----------------------------------------------------------------------------------------
-- Task success and failure keep the structural invariant independent of error accounting
-----------------------------------------------------------------------------------------

/-- Successful task handling preserves structural retirement and emitted notice ancestry.
Witness: matched child integration, protected successful closures, activation, and drain.
Absent tasks produce no output; present tasks follow the same success path.
-/
private theorem RetirementFrame.taskSuccess_with_notices {queue : State} {work parents}
    (prior : RetirementFrame queue work parents)
    (registration : queue.RegistrationFrame work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : RetirementFrame (queue.taskSuccess occurrence result available).1 work parents
      ∧ (queue.taskSuccess occurrence result available).1.GroupNoticeAncestorsRetired work
          (queue.taskSuccess occurrence result available).2.1 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskSuccess, found]
        using And.intro prior (State.GroupNoticeAncestorsRetired.of_noNotices (by simp))
  | some taskNode =>
      rw [queue.taskSuccess_eq occurrence result taskNode found available]
      let stored := queue.putTaskNode { taskNode with value := some result.value }
      have storedFrame : RetirementFrame stored work parents :=
        ⟨prior.groups, prior.links, prior.live, prior.tasks, prior.roots, prior.retired⟩
      have registeredTask := registration.started taskNode (List.mem_of_find?_eq_some found)
      have identity := (State.taskNode?_some found).2
      have certificate := (registration.children taskNode.task registeredTask).sourceChild identity matching
      have integrated := storedFrame.maybeIntegrateWork result.work
        (fun _ member => matching.taskChildGroups_recordAt member)
        (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
        certificate.contributors (some occurrence) generated canonical certificate.parentRefs
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
      have activated := finalFrame.startNewWork final.2.2 protectedRoots.2 available
      have noticed := State.successGroupFold_noticeAncestorRetirement protectedRoots.2
      exact ⟨activated.drainReadyGroups generated canonical available,
        (noticed.mono (fun _ retired =>
          (retired.startNewWork _ available).drainReadyGroups available)).append
          (activated.drainReadyGroups_noticeRetirement generated canonical available)⟩

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
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (available : List (Occurrence × Nat) := [])
    : RetirementFrame (queue.integrateStreamItem item available) work parents
      ∧ ∀ child ∈
          ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
            (queue.maybeIntegrateWork item.work).2.newGroups).2,
          (queue.integrateStreamItem item available).AncestorsRetired work child.ref := by
  let integrated := queue.maybeIntegrateWork item.work
  have integratedFrame : RetirementFrame integrated.1 work parents :=
    prior.maybeIntegrateWork item.work
      (fun _ candidate => matching.streamItem_childGroups_recordAt member candidate)
      (fun _ candidate => matching.streamItem_childGroups_parentCanonical canonical
        member candidate) (by
          intro task taskMember ref contributor
          exact Or.inr (matching.streamItem_childTasksCovered generated.declarations member
            task taskMember ref contributor)) none generated canonical
      (generated.declarations.sourceStreamItem matching member queue.registeredGroups).parentRefs
  have protectedRoots : ∀ node ∈ integrated.2.newGroups,
      integrated.1.AncestorsRetired work node.ref := by
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
  exact ⟨
    prunedFrame.startNewWork { integrated.2 with newGroups := pruned.2 } prunedRoots
      available,
    fun child member =>
      (prunedRoots child member).mono (fun _ retired => retired.startNewWork _ available)
  ⟩

/-- Sequential item integration retains structural retirement before any drain output.
Witness: induction over the actual integration fold with each item's matching evidence.
-/
private theorem RetirementFrame.streamItemFold_with_notices {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : let prepared :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (queue, [], [], [], [])
      RetirementFrame prepared.1 work parents
      ∧ ∀ child ∈ prepared.2.1, prepared.1.AncestorsRetired work child.ref := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (invariant : RetirementFrame acc.1 work parents)
      (protectedRoots : ∀ child ∈ acc.2.1, acc.1.AncestorsRetired work child.ref)
      : RetirementFrame (more.foldl (fun acc item => streamItemStep acc item available) acc).1
          work parents
        ∧ ∀ child ∈ (more.foldl (fun acc item => streamItemStep acc item available) acc).2.1,
          (more.foldl (fun acc item => streamItemStep acc item available) acc).1.AncestorsRetired
            work child.ref := by
    induction more generalizing acc with
    | nil => exact ⟨invariant, protectedRoots⟩
    | cons item rest ih =>
        have integrated := invariant.integrateStreamItem_with_notices generated canonical
          matching (included List.mem_cons_self) available
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) _ integrated.1
        intro child member
        rcases List.mem_append.mp member with old | new
        · exact (protectedRoots child old).mono (fun _ retired =>
            ((retired.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available)
        · exact integrated.2 child new
  exact loop items (fun _ member => member) (queue, [], [], [], []) prior (by simp)

/-- Item handling retains notice ancestry through preparation and its subsequent drain.
Witness: combine the exact preparation frontier with the independent drain theorem,
transporting earlier ancestor retirements through later successful or failing cleanup.
-/
private theorem RetirementFrame.streamItems_with_notices {queue : State} {work parents}
    (prior : RetirementFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : RetirementFrame (queue.streamItems stream items available).1 work parents
      ∧ (queue.streamItems stream items available).1.GroupNoticeAncestorsRetired work
          (queue.streamItems stream items available).2.1 := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact ⟨prior, .of_noNotices (by simp)⟩
  · have folded := prior.streamItemFold_with_notices generated canonical matching available
    refine ⟨folded.1.drainReadyGroups generated canonical available, ?_⟩
    let final := items.foldl (fun acc item => streamItemStep acc item available)
      (queue, [], [], [], [])
    change (final.1.drainReadyGroups available).1.GroupNoticeAncestorsRetired work
      ([.streamValues stream final.2.2.2.1 final.2.1 final.2.2.1]
        ++ (final.1.drainReadyGroups available).2.1)
    apply State.GroupNoticeAncestorsRetired.append
    · intro ref member
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, rawGroupNoticeRefs]
        at member
      obtain ⟨child, noticed, same⟩ := List.mem_map.mp member
      exact same ▸ (folded.2 child noticed).mono
        (fun _ retired => retired.drainReadyGroups available)
    · exact folded.1.drainReadyGroups_noticeRetirement generated canonical available

-----------------------------------------------------------------------------------------
-- Compose all actual input handlers and publisher-normalized host batches
-----------------------------------------------------------------------------------------

/-- Every matched event preserves the structural retirement frame.
Witness: success/item certificates and cancellation-marked failure removal; stream closure
does not modify group structure. Source timing and acceptance are not assumptions.
-/
private theorem RetirementFrame.handleGraphEvent {queue : State} {work parents}
    (prior : RetirementFrame queue work parents)
    (registration : queue.RegistrationFrame work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : RetirementFrame (queue.handleGraphEvent event available).1 work parents := by
  let current := queue.cacheTaskFailures available
  have cached := prior.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      exact (cached.taskSuccess_with_notices (registration.cacheTaskFailures available) generated canonical matching available).1
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items =>
      exact (cached.streamItems_with_notices generated canonical matching available).1
  | streamSuccess stream =>
      change RetirementFrame (current.streamSuccess stream).1 work parents
      unfold State.streamSuccess
      split <;> exact ⟨cached.groups, cached.links, cached.live, cached.tasks,
        cached.roots, cached.retired⟩
  | streamFailure stream errors =>
      change RetirementFrame (current.streamFailure stream errors).1 work parents
      unfold State.streamFailure
      split <;> exact ⟨cached.groups, cached.links, cached.live, cached.tasks,
        cached.roots, cached.retired⟩

  | groupFailure notice =>
      change RetirementFrame (current.groupFailure notice).1 work parents
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact ⟨cached.groups, cached.links, cached.live, cached.tasks,
          cached.roots, cached.retired⟩

/-- Startup enqueue effects preserve the structural retirement frame. -/
private theorem RetirementFrame.dispatchGraphEvent {queue : State} {work parents}
    (prior : RetirementFrame queue work parents)
    (registration : queue.RegistrationFrame work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : RetirementFrame (queue.dispatchGraphEvent event available).1 work parents := by
  have next := prior.handleGraphEvent registration generated canonical event matching available
  exact ⟨next.groups, next.links, next.live, next.tasks, next.roots, next.retired⟩

/-- Every actual handler retains the retired ancestry of its carried group notices.
Witness: the two notice-producing handlers supply certificates; the other handlers have
empty group-notice projections, independently of successful or failing payloads.
-/
private theorem RetirementFrame.handleGraphEvent_noticeRetirement
    {queue : State} {work parents}
    (prior : RetirementFrame queue work parents)
    (registration : queue.RegistrationFrame work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.GroupNoticeAncestorsRetired work
        (queue.handleGraphEvent event available).2.1 := by
  let current := queue.cacheTaskFailures available
  have cached := prior.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      exact (cached.taskSuccess_with_notices (registration.cacheTaskFailures available) generated canonical matching available).2
  | streamItems stream items =>
      exact (cached.streamItems_with_notices generated canonical matching available).2
  | taskFailure occurrence errors =>
      change (current.taskFailure occurrence errors).1.GroupNoticeAncestorsRetired work
        (current.taskFailure occurrence errors).2
      intro ref member
      rw [State.taskFailure_groupNotices] at member
      cases member
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [State.GroupNoticeAncestorsRetired, rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [State.GroupNoticeAncestorsRetired, rawGroupNoticeRefs]

  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simp [State.GroupNoticeAncestorsRetired]
      · split <;> simp [State.GroupNoticeAncestorsRetired, rawGroupNoticeRefs]

/-- Sequential source replay preserves the same structural frame without batch controls.
Witness: fold over matched actual event handlers; termination flags are irrelevant here.
-/
private theorem RetirementFrame.replayGraphEvents {queue : State} {work parents}
    (prior : RetirementFrame queue work parents)
    (registration : queue.RegistrationFrame work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : RetirementFrame (queue.replayGraphEvents events available) work parents := by
  induction events generalizing queue with
  | nil => exact prior
  | cons event rest ih =>
      exact ih (prior.dispatchGraphEvent registration generated canonical event
        (matching event List.mem_cons_self) available)
        (registration.dispatchGraphEvent event (matching event List.mem_cons_self) available).1
        (fun next member => matching next (List.mem_cons_of_mem _ member))

/-- A matched host batch retains the frame at each concrete handler state.
Witness: event-fold induction, followed only by an optional termination-flag update.
-/
private theorem RetirementFrame.handleGraphEvents {queue : State} {work parents}
    (prior : RetirementFrame queue work parents)
    (registration : queue.RegistrationFrame work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : RetirementFrame (queue.handleGraphEvents events).1 work parents := by
  cases running : queue.terminated with
  | true => simpa only [State.handleGraphEvents, running, ↓reduceIte] using prior
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      have final := prior.replayGraphEvents registration generated canonical events matching
        (GraphEvent.availableFailures events)
      rw [same]
      exact ⟨final.groups, final.links, final.live, final.tasks, final.roots, final.retired⟩

/-- Publisher normalization preserves the queue's structural frame across matched batches.
Witness: the publisher leaves queue fields unchanged after each actual host-batch handler.
-/
private theorem RetirementFrame.runNormalized {queue : State} {work parents}
    (prior : RetirementFrame queue work parents)
    (registration : queue.RegistrationFrame work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : RetirementFrame (queue.runNormalized batches).1 work parents := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue with
  | nil => exact prior
  | cons batch rest ih =>
      have matched := matching batch List.mem_cons_self
      exact ih (prior.handleGraphEvents registration generated canonical batch matched)
        (registration.handleGraphEvents batch matched).1
        (fun more member => matching more (List.mem_cons_of_mem _ member))

/-- Item preparation preserves the structural retirement frame at the actual drain
entry, for an arbitrary prior queue satisfying those internal invariants.
-/
theorem State.preparedStreamItems_structuralRetirement {queue : State} {work parents}
    (generated : ExecutedWork work) (groups : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (retired : queue.UncancelledRetiredAncestors work) {stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : let prepared := queue.preparedStreamItems items available
      prepared.GroupNodesMatchWork work
      ∧ prepared.ChildLinksCanonical parents
      ∧ prepared.LiveGroupsRegistered
      ∧ prepared.TaskGroupsRegistered
      ∧ prepared.RootAncestorsRetired work
      ∧ prepared.UncancelledRetiredAncestors work := by
  have prior : RetirementFrame queue work parents := ⟨groups, links, live, tasks, roots, retired⟩
  have prepared := State.preparedStreamItems_preserves
    (fun current => RetirementFrame current work parents) prior items available
    (fun _ _ member frame =>
      (frame.integrateStreamItem_with_notices generated canonical matching member available).1)
  exact ⟨prepared.groups, prepared.links, prepared.live, prepared.tasks,
    prepared.roots, prepared.retired⟩

/-- A matched handler preserves the structural certificates needed by owner replay.
The result is derived from its actual cache-aware transition, without a health premise.
-/
theorem State.handleGraphEvent_structuralRetirement {queue : State} {work parents}
    (generated : ExecutedWork work) (groups : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (registration : queue.RegistrationFrame work)
    (roots : queue.RootAncestorsRetired work)
    (retired : queue.UncancelledRetiredAncestors work) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.LiveGroupsRegistered
      ∧ (queue.handleGraphEvent event available).1.RootAncestorsRetired work
      ∧ (queue.handleGraphEvent event available).1.UncancelledRetiredAncestors work := by
  have prior : RetirementFrame queue work parents := ⟨groups, links, live, tasks, roots, retired⟩
  have next := prior.handleGraphEvent registration generated canonical event matching available
  exact ⟨next.live, next.roots, next.retired⟩

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
  have registered := createWorkQueue_registration work generated.declarations
  have declarationFrame := State.initialize_registrationFrame generated.declarations
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical_root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have final := initial.runNormalized declarationFrame generated canonical batches matching
  exact ⟨final.roots, final.retired⟩

/-- Sequential matched replay retains root and uncancelled ancestor certificates.
Witness: generated initialization and the same structural handler induction, without
requiring accepted input, completed output, or a selected schedule.
-/
theorem ExecutedWork.replayGraphEvents_structuralRetirement {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : let queue :=
        (State.initialize (Work.fromExecution work)).replayGraphEvents events available
      queue.RootAncestorsRetired work ∧ queue.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work generated.declarations
  have declarationFrame := State.initialize_registrationFrame generated.declarations
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical_root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have final := initial.replayGraphEvents declarationFrame generated canonical events matching available
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
    (available : List (Occurrence × Nat) := [])
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        (before ++ [event]) available).GroupNoticeAncestorsRetired
        work
        (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before available).handleGraphEvent
          event available).2.1 := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work generated.declarations
  have declarationFrame := State.initialize_registrationFrame generated.declarations
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical_root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have prior := initial.replayGraphEvents declarationFrame generated canonical before matching available
  have noticed := prior.handleGraphEvent_noticeRetirement
    (declarationFrame.replayGraphEvents before matching available).1 generated canonical event incoming
    available
  have dispatched : (((State.initialize (Work.fromExecution work)).replayGraphEvents before
      available).dispatchGraphEvent event available).1.GroupNoticeAncestorsRetired work
        (((State.initialize (Work.fromExecution work)).replayGraphEvents before available).handleGraphEvent
          event available).2.1 := noticed.mono (fun _ retired => retired)
  simpa only [State.replayGraphEvents, List.foldl_append, List.foldl_cons, List.foldl_nil]
    using dispatched

/-- A matched successful input's prepared state has all structural release certificates.
Witness: the same generated replay frame, followed only by value installation and matched
child integration. No buffered-value, failure-health, or publication premise is needed.
-/
theorem ExecutedWork.replayGraphEvents_preparedRetirement {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work) {occurrence result}
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (node : TaskNode)
    (available : List (Occurrence × Nat) := [])
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          events available).taskNode?
          occurrence
        = some node)
    : let queue :=
        (State.initialize (Work.fromExecution work)).replayGraphEvents events available
      let prepared :=
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      ∃ parents,
        (∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
        ∧ prepared.GroupNodesMatchWork work
        ∧ prepared.ChildLinksCanonical parents
        ∧ prepared.LiveGroupsRegistered
        ∧ prepared.TaskGroupsRegistered
        ∧ prepared.RootAncestorsRetired work
        ∧ prepared.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work generated.declarations
  have declarationFrame := State.initialize_registrationFrame generated.declarations
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical_root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have prior := initial.replayGraphEvents declarationFrame generated canonical events matching available
  have stored : RetirementFrame
      (((State.initialize (Work.fromExecution work)).replayGraphEvents events available).putTaskNode
        { node with value := some result.value }) work parents :=
    ⟨prior.groups, prior.links, prior.live, prior.tasks, prior.roots, prior.retired⟩
  have replayed := (declarationFrame.replayGraphEvents events matching available).1
  have certificate := (replayed.children node.task
    (replayed.started node (List.mem_of_find?_eq_some found))).sourceChild
      (State.taskNode?_some found).2 matched
  have prepared := stored.maybeIntegrateWork result.work
    (fun _ member => matched.taskChildGroups_recordAt member)
    (fun _ member => matched.taskChildGroups_parentCanonical canonical member)
    certificate.contributors (some occurrence) generated canonical certificate.parentRefs
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
    (available : List (Occurrence × Nat) := [])
    : let queue :=
        (State.initialize (Work.fromExecution work)).replayGraphEvents events available
      let prepared := queue.preparedStreamItems items available
      ∃ parents,
        (∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
        ∧ prepared.GroupNodesMatchWork work
        ∧ prepared.ChildLinksCanonical parents
        ∧ prepared.LiveGroupsRegistered
        ∧ prepared.TaskGroupsRegistered
        ∧ prepared.RootAncestorsRetired work
        ∧ prepared.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work generated.declarations
  have declarationFrame := State.initialize_registrationFrame generated.declarations
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical_root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have prior := initial.replayGraphEvents declarationFrame generated canonical events matching available
  have prepared := State.preparedStreamItems_preserves
    (fun current => RetirementFrame current work parents) prior items available
    (fun _ _ member frame =>
      (frame.integrateStreamItem_with_notices generated canonical matched member available).1)
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
    (available : List (Occurrence × Nat) := [])
    : let queue :=
        (State.initialize (Work.fromExecution work)).replayGraphEvents before available
      let prepared :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (queue, [], [], [], [])
      ∀ child ∈ prepared.2.1, prepared.1.AncestorsRetired work child.ref := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work generated.declarations
  have declarationFrame := State.initialize_registrationFrame generated.declarations
  have initial : RetirementFrame (State.initialize (Work.fromExecution work)) work parents :=
    ⟨createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical_root canonical member),
      registered.1, registered.2, generated.initialRootAncestorsRetired,
      generated.initialUncancelledRetirement⟩
  have prior := initial.replayGraphEvents declarationFrame generated canonical before matching available
  exact (prior.streamItemFold_with_notices generated canonical matched available).2

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
        work (GraphEvent.failureSettlements batches.flatten) :=
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
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
    ).runNormalized batches matching canonical
  exact closure.missingParent generated valid.runNormalized_groupNodesMatchWork parentFields
    canonical (generated.runNormalized_parentsRegistered valid)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
