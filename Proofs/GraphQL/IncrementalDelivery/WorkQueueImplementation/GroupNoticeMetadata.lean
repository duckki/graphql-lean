import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPruningNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupSupportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationCandidates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeMetadata

/-! Every carried group notice denotes a real contributor, including promoted descendants. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Local metadata combines exact records with the pruning gate's contributor support
-----------------------------------------------------------------------------------------

/-- Every group descriptor announced by this raw event is an actual work node.
Registration-only ancestor shells are deliberately excluded from this predicate.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.GroupNoticesLocated
    (work : Execution.Work) : WorkQueueEvent → Prop
  | .groupSuccess _ groups _ | .streamValues _ _ groups _ =>
      ∀ group ∈ groups,
        ∃ dependencies producer, NodeAt work group .group dependencies producer
  | _ => True

/-- The three independently derived state facts used to inspect a pruning boundary.
This proof package introduces no executable state or host-source premise.
-/
structure NoticeFrame (work : Execution.Work) (queue : State) : Prop where
  refs : queue.GroupRefsUnique
  records : queue.GroupNodesMatchWork work
  support
    : queue.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)

/-- Successful flushing preserves the frame and certifies both its output and releases.
Witness: exact post-pruning contents exclude shells; the implementation copies that
same pruned list into its completion event and its activation result.
-/
private theorem NoticeFrame.finishGroupSuccess {work queue}
    (frame : NoticeFrame work queue) (generated : ExecutedWork work) (node : GroupNode)
    : NoticeFrame work (queue.finishGroupSuccess node).1
      ∧ (∀ event ∈ (queue.finishGroupSuccess node).2.1, event.GroupNoticesLocated work)
      ∧ ∀ group ∈ (queue.finishGroupSuccess node).2.2.newGroups,
          ∃ dependencies producer, NodeAt work group .group dependencies producer := by
  have released := fun group member =>
    (queue.finishGroupSuccess_noticeContents generated frame.refs frame.records
      frame.support node (child := group) member).1
  refine ⟨⟨frame.refs.finishGroupSuccess node, frame.records.finishGroupSuccess node,
    (frame.support.finishGroupSuccess node).1⟩, ?_, released⟩
  obtain ⟨values, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  intro event member
  rw [output] at member
  rcases List.mem_append.mp member with value | closure
  · split at value
    · cases value
    · obtain rfl := List.mem_singleton.mp value
      trivial
  · obtain rfl := List.mem_singleton.mp closure
    exact released

/-- Cache exposure leaves notice metadata unchanged.
Witness: only task-local rejections change; identities, records and support remain intact.
-/
private theorem NoticeFrame.cacheTaskFailures {work queue}
    (frame : NoticeFrame work queue) (available : List (Occurrence × Nat))
    : NoticeFrame work (queue.cacheTaskFailures available) :=
  ⟨
    frame.refs.cacheTaskFailures available,
    frame.records.cacheTaskFailures available,
    frame.support.cacheTaskFailures available
  ⟩

/-- Starting pruned work preserves descriptor provenance for all surviving records.
Witness: startup may remove failed groups; it introduces no group descriptor. Root support
comes from the just-proved notice provenance, independently of output admission.
-/
private theorem NoticeFrame.startNewWork {work queue}
    (frame : NoticeFrame work queue) (newWork : NewWork)
    (known
      : ∀ group ∈ newWork.newGroups,
          ∃ dependencies producer, NodeAt work group .group dependencies producer)
    (available : List (Occurrence × Nat) := [])
    : NoticeFrame work (queue.startNewWork newWork available).1 := by
  refine ⟨frame.refs.startNewWork newWork available, frame.records.startNewWork newWork available,
    frame.support.startNewWork newWork ?_ available⟩
  intro group member
  obtain ⟨dependencies, producer, located⟩ := known group member
  exact ⟨dependencies, group, producer, located, rfl⟩

-----------------------------------------------------------------------------------------
-- Recursive drains preserve provenance at every internal release boundary
-----------------------------------------------------------------------------------------

/-- Successful flushing and child activation retain the metadata for the next drain step.
Witness: the pruning result contains only actual contributors, which supplies the root
support needed for activation. No announcement-admission premise is used.
-/
theorem State.finishGroupSuccess_activated_noticeMetadata {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (node : GroupNode) (available : List (Occurrence × Nat) := [])
    : let finished := queue.finishGroupSuccess node
      let current := (finished.1.startNewWork finished.2.2 available).1
      current.GroupRefsUnique
      ∧ current.GroupNodesMatchWork work
      ∧ current.GroupRefSupport
          (fun ref =>
            ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  obtain ⟨frame, _, released⟩ :=
    NoticeFrame.finishGroupSuccess ⟨refs, records, support⟩ generated node
  have activated := frame.startNewWork _ released available
  exact ⟨activated.refs, activated.records, activated.support⟩

/-- The drain never announces an ancestor-only shell, including after recursive promotion.
Witness: each successful closure passes through the pruning certificate; failed closures
have no notices. The same frame is retained for the recursive queue boundary.
-/
private theorem NoticeFrame.drainReadyGroups {work queue}
    (frame : NoticeFrame work queue) (generated : ExecutedWork work)
    (available : List (Occurrence × Nat) := [])
    : NoticeFrame work (queue.drainReadyGroups available).1
      ∧ ∀ event ∈ (queue.drainReadyGroups available).2.1,
          event.GroupNoticesLocated work := by
  have loop (fuel : Nat) (current : State) (known : NoticeFrame work current)
      : NoticeFrame work (State.drainReadyGroups.go available fuel current).1
        ∧ ∀ event ∈ (State.drainReadyGroups.go available fuel current).2.1,
            event.GroupNoticesLocated work := by
    induction fuel generalizing current with
    | zero => exact ⟨known, by simp [State.drainReadyGroups.go]⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨known, by simp⟩
        · rename_i node selected
          obtain ⟨next, outputs, released⟩ := known.finishGroupSuccess generated node
          obtain ⟨final, later⟩ := ih _ (next.startNewWork _ released available)
          exact ⟨final, fun event member =>
            (List.mem_append.mp member).elim (outputs event) (later event)⟩
  exact loop _ queue frame

/-- All notices emitted by a ready drain denote actual generated-work nodes.
Witness: combine independently proved state metadata and project the local drain result.
-/
theorem State.drainReadyGroups_groupNoticesLocated {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (available : List (Occurrence × Nat) := [])
    : ∀ event ∈ (queue.drainReadyGroups available).2.1, event.GroupNoticesLocated work :=
  (NoticeFrame.drainReadyGroups ⟨refs, records, support⟩ generated available).2

-----------------------------------------------------------------------------------------
-- The task-success owner's single pass and the item-integration fold use the same gate
-----------------------------------------------------------------------------------------

/-- Integration preserves the frame using supplied descriptor and task provenance.
Witness: group shells retain records, while only actual task owners can acquire contents.
-/
private theorem NoticeFrame.maybeIntegrateWork {work queue}
    (frame : NoticeFrame work queue) (newWork : Work)
    (records
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (owners
      : ∀ task ∈ newWork.tasks,
        ∀ group ∈ task.groups,
          ∃ dependencies, NodeHasDependencies work group.ref .group dependencies)
    (parentTask : Option Occurrence := none)
    : NoticeFrame work (queue.maybeIntegrateWork newWork parentTask).1 :=
  ⟨
    frame.refs.maybeIntegrateWork newWork parentTask,
    frame.records.maybeIntegrateWork newWork records parentTask,
    frame.support.maybeIntegrateWork newWork owners parentTask
  ⟩

/-- Every contributor-fold notice has an actual node before final child activation.
Witness: decrementing a counter changes no task/error contents; successful flushes pass
through the pruning gate. The accumulated release list retains the same provenance.
-/
private theorem NoticeFrame.successGroupFold {work queue}
    (frame : NoticeFrame work queue) (generated : ExecutedWork work)
    (groups : List Execution.DeliveryNode)
    : let result := groups.foldl successGroupStep (queue, [], {})
      NoticeFrame work result.1
      ∧ (∀ event ∈ result.2.1, event.GroupNoticesLocated work)
      ∧ ∀ group ∈ result.2.2.newGroups,
          ∃ dependencies producer, NodeAt work group .group dependencies producer := by
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (known : NoticeFrame work acc.1)
      (outputs : ∀ event ∈ acc.2.1, event.GroupNoticesLocated work)
      (released : ∀ group ∈ acc.2.2.newGroups,
        ∃ dependencies producer, NodeAt work group .group dependencies producer)
      : let result := more.foldl successGroupStep acc
        NoticeFrame work result.1
          ∧ (∀ event ∈ result.2.1, event.GroupNoticesLocated work)
          ∧ ∀ group ∈ result.2.2.newGroups,
              ∃ dependencies producer, NodeAt work group .group dependencies producer := by
    induction more generalizing acc with
    | nil => exact ⟨known, outputs, released⟩
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih acc known outputs released
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have decremented : NoticeFrame work (acc.1.putGroupNode updated) :=
            ⟨known.refs.putGroupNode updated,
              known.records.putGroupNode updated
                (known.records node (List.mem_of_find?_eq_some found)),
              known.support.putGroupNode updated (by
                intro absent
                exact known.support.contents node (List.mem_of_find?_eq_some found) absent)⟩
          split
          · obtain ⟨next, notices, children⟩ :=
              decremented.finishGroupSuccess generated updated
            exact ih _ next
              (fun event member => (List.mem_append.mp member).elim
                (outputs event) (notices event))
              (fun child member => (List.mem_append.mp member).elim
                (released child) (children child))
          · exact ih _ decremented outputs released
  exact loop groups (queue, [], {}) frame (by simp) (by simp)

/-- Every owner-fold prefix retains the metadata needed to inspect its notice contents.
Witness: project the existing local frame-preservation induction. This exposes state
metadata only, not notice eligibility or any additional source assumption.
-/
theorem State.successGroupFold_noticeMetadata {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (groups : List Execution.DeliveryNode)
    : let current := (groups.foldl successGroupStep (queue, [], {})).1
      current.GroupRefsUnique
      ∧ current.GroupNodesMatchWork work
      ∧ current.GroupRefSupport
          (fun ref =>
            ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  have frame := (NoticeFrame.successGroupFold ⟨refs, records, support⟩ generated groups).1
  exact ⟨frame.refs, frame.records, frame.support⟩

/-- Every owner-fold notice names an actual contributing work node.
Witness: project notice provenance from the same metadata-preservation induction used
for the queue state; no output-admission or freshness assumption is introduced.
-/
theorem State.successGroupFold_groupNoticesLocated {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (groups : List Execution.DeliveryNode)
    : ∀ event ∈ (groups.foldl successGroupStep (queue, [], {})).2.1,
        event.GroupNoticesLocated work :=
  (NoticeFrame.successGroupFold ⟨refs, records, support⟩ generated groups).2.1

/-- A matching successful task emits only real contributor notices.
Witness: matched child work supplies the integration metadata, the actual single-pass
owner fold certifies its releases, and the subsequent ready drain preserves that evidence.
-/
theorem State.taskSuccess_groupNoticesLocated {queue : State} {work occurrence result}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ∀ event ∈ (queue.taskSuccess occurrence result available).2.1,
        event.GroupNoticesLocated work := by
  unfold State.taskSuccess
  split
  · simp
  · rename_i taskNode found
    let stored := queue.putTaskNode { taskNode with value := some result.value }
    have old : NoticeFrame work stored :=
      ⟨refs, records, ⟨support.contents, support.roots⟩⟩
    have integrated := old.maybeIntegrateWork result.work
      (fun _ member => matching.taskChildGroups_recordAt member)
      (by
        intro task member group owner
        obtain ⟨address, payload, occurrenceEq, located⟩ := matching.childTask_producer member
        have taskKnown : TaskMatches work task :=
          ⟨⟨address, payload, some occurrence, occurrenceEq, located⟩,
            matching.childTask_groupsExact member⟩
        exact taskKnown.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩))
      (some occurrence)
    obtain ⟨folded, emitted, released⟩ :=
      integrated.successGroupFold generated taskNode.task.groups
    have drained := (folded.startNewWork _ released available).drainReadyGroups generated available
    exact fun event member => (List.mem_append.mp member).elim (emitted event) (drained.2 event)

/-- Each integrated item's pruned notices denote real contributors, not ancestor shells.
Witness: input provenance includes promoted ancestors; pruning preserves descriptors and
uses task contents to recover actual structural nodes before activation.
-/
private theorem NoticeFrame.integrateStreamItem {work queue stream items item}
    (frame : NoticeFrame work queue) (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items) (available : List (Occurrence × Nat) := [])
    : let integrated := queue.maybeIntegrateWork item.work
      let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
      NoticeFrame work
        (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 } available).1
      ∧ ∀ group ∈ pruned.2,
          ∃ dependencies producer, NodeAt work group .group dependencies producer := by
  have records := fun group candidate => matching.streamItem_childGroups_recordAt member
    (group := group) candidate
  have integrated := frame.maybeIntegrateWork item.work records (by
    intro task candidate group owner
    obtain ⟨address, payload, occurrenceEq, located⟩ :=
      matching.streamItem_childTask_producer member candidate
    have taskKnown : TaskMatches work task :=
      ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
        matching.streamItem_childTask_groupsExact member candidate⟩
    exact taskKnown.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩))
  let current := queue.maybeIntegrateWork item.work
  have candidates : ∀ group ∈ current.2.newGroups,
      ∃ dependencies, GroupRecordAt work group dependencies := by
    intro group noticed
    obtain ⟨record, candidate, same, _⟩ :=
      queue.addGroups_newGroup_candidate item.work.groups noticed
    exact same ▸ records record candidate
  have located := fun group member =>
    (current.1.pruneEmptyGroups_noticeContents generated integrated.refs integrated.records
      integrated.support current.2.newGroups candidates (group := group) member).1
  have pruned : NoticeFrame work (current.1.pruneEmptyGroups current.2.newGroups).1 :=
    ⟨integrated.refs.pruneEmptyGroups _, integrated.records.pruneEmptyGroups _,
      (integrated.support.pruneEmptyGroups _).1⟩
  exact ⟨pruned.startNewWork _ located available, located⟩

/-- An item's new notice retains concrete contents at its own integration boundary.
Witness: matching child work supplies group records and contributors; the actual pruning
gate retains a nonempty record before startup can remove a failed group.
-/
theorem State.integrateStreamItem_noticeContents {queue : State}
    {work stream items item child}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items)
    (noticed
      : child
        ∈ ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
            (queue.maybeIntegrateWork item.work).2.newGroups).2)
    : (∃ dependencies producer, NodeAt work child .group dependencies producer)
      ∧ ∃ node,
          ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
              (queue.maybeIntegrateWork item.work).2.newGroups).1.groupNode?
              child.ref
            = some node
          ∧ node.group.node = child
          ∧ node.tasks ≠ [] := by
  have frame : NoticeFrame work queue := ⟨refs, records, support⟩
  have childRecords := fun group candidate =>
    matching.streamItem_childGroups_recordAt member (group := group) candidate
  have integrated := frame.maybeIntegrateWork item.work childRecords (by
    intro task candidate group owner
    obtain ⟨address, payload, occurrenceEq, located⟩ :=
      matching.streamItem_childTask_producer member candidate
    have known : TaskMatches work task :=
      ⟨⟨address, payload, some item.occurrence, occurrenceEq, located⟩,
        matching.streamItem_childTask_groupsExact member candidate⟩
    exact known.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩))
  have candidates : ∀ group ∈ (queue.maybeIntegrateWork item.work).2.newGroups,
      ∃ dependencies, GroupRecordAt work group dependencies := by
    intro group announced
    obtain ⟨record, candidate, same, _⟩ :=
      queue.addGroups_newGroup_candidate item.work.groups announced
    exact same ▸ childRecords record candidate
  obtain ⟨known, node, found, same, contents⟩ :=
    (queue.maybeIntegrateWork item.work).1.pruneEmptyGroups_noticeContents generated
      integrated.refs integrated.records integrated.support _ candidates noticed
  exact ⟨known, node, found, same, contents⟩

/-- Item-carried and recursively drained group notices all have actual work provenance.
Witness: induction on the real item fold retains each pruned descriptor and the registry
frame. The leading item event carries exactly those descriptors; draining handles the rest.
-/
theorem State.streamItems_groupNoticesLocated {queue : State} {work stream items}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ∀ event ∈ (queue.streamItems stream items available).2.1,
        event.GroupNoticesLocated work := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (frame : NoticeFrame work acc.1)
      (notices : ∀ group ∈ acc.2.1,
        ∃ dependencies producer, NodeAt work group .group dependencies producer)
      : NoticeFrame work (more.foldl (fun acc item => streamItemStep acc item available) acc).1
        ∧ ∀ group ∈ (more.foldl (fun acc item => streamItemStep acc item available) acc).2.1,
            ∃ dependencies producer, NodeAt work group .group dependencies producer := by
    induction more generalizing acc with
    | nil => exact ⟨frame, notices⟩
    | cons item rest ih =>
        obtain ⟨next, children⟩ := frame.integrateStreamItem generated matching
          (included List.mem_cons_self) available
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _ next
          (fun group member => (List.mem_append.mp member).elim (notices group) (children group))
  rw [queue.streamItems_eq stream items available]
  split
  · simp
  · obtain ⟨prepared, notices⟩ := loop items (List.Subset.refl _) (queue, [], [], [], [])
      ⟨refs, records, support⟩ (by simp)
    intro event member
    rcases List.mem_cons.mp member with rfl | later
    · exact notices
    · exact (prepared.drainReadyGroups generated available).2 event later

-----------------------------------------------------------------------------------------
-- Source replay and publisher normalization retain the same notice descriptors
-----------------------------------------------------------------------------------------

/-- Actual item preparation retains its complete structural notice metadata under the
supplied snapshot, including groups removed before their queued notices are forwarded.
-/
theorem State.preparedStreamItems_noticeMetadata {queue : State} {work stream items}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).GroupRefsUnique
      ∧ (queue.preparedStreamItems items available).GroupNodesMatchWork work
      ∧ (queue.preparedStreamItems items available).GroupRefSupport
          (fun ref =>
            ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  have prepared := State.preparedStreamItems_preserves (NoticeFrame work)
    ⟨refs, records, support⟩ items available
    (fun _ _ member frame => (frame.integrateStreamItem generated matching member available).1)
  exact ⟨prepared.refs, prepared.records, prepared.support⟩

/-- Every matching handler emits only group notices with actual structural provenance.
Witness: the two value handlers use the pruning gate; all other handlers announce nothing.
-/
theorem State.handleGraphEvent_groupNoticesLocated {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ∀ output ∈ (queue.handleGraphEvent event available).2.1,
        output.GroupNoticesLocated work := by
  have cached : NoticeFrame work (queue.cacheTaskFailures available) :=
    (NoticeFrame.mk refs records support).cacheTaskFailures available
  unfold State.handleGraphEvent
  cases event with
  | taskSuccess occurrence result =>
      exact State.taskSuccess_groupNoticesLocated generated cached.refs cached.records
        cached.support matching available
  | streamItems stream items =>
      exact State.streamItems_groupNoticesLocated generated cached.refs cached.records
        cached.support matching available
  | taskFailure occurrence errors =>
      intro output member
      cases output with
      | groupSuccess group groups streams =>
          exact False.elim ((queue.cacheTaskFailures available).taskFailure_noGroupSuccess
            occurrence errors group groups streams
            member)
      | streamValues stream values groups streams =>
          have impossible : stream.ref ∈
              ((queue.cacheTaskFailures available).taskFailure
                occurrence errors).2.flatMap rawStreamReferenceRefs :=
            List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩
          rw [State.taskFailure_streamReferences] at impossible
          cases impossible
      | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination
        =>
          trivial
  | streamSuccess stream =>
      simp only [State.streamSuccess]
      split <;> simp [WorkQueueEvent.GroupNoticesLocated]
  | streamFailure stream errors =>
      simp only [State.streamFailure]
      split <;> simp [WorkQueueEvent.GroupNoticesLocated]

  | groupFailure failure =>
      simp only [State.groupFailure]
      split
      · simp
      · split <;> simp [WorkQueueEvent.GroupNoticesLocated]

/-- Replay keeps the task registries needed to justify contributor support at later inputs.
These are derived bookkeeping invariants, not stronger source semantics.
-/
structure NoticeReplayFrame (work : Execution.Work) (queue : State) : Prop where
  notices : NoticeFrame work queue
  started : queue.StartedTasksRegistered
  tasks : queue.RegisteredTasksMatch work

/-- One host event preserves the joint frame and certifies its actual output notices.
Witness: compose independent state-preservation proofs with local notice provenance.
-/
private theorem NoticeReplayFrame.handleGraphEvent {work queue}
    (frame : NoticeReplayFrame work queue) (generated : ExecutedWork work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : NoticeReplayFrame work (queue.handleGraphEvent event available).1
      ∧ ∀ output ∈ (queue.handleGraphEvent event available).2.1,
          output.GroupNoticesLocated work :=
  ⟨
    ⟨
      ⟨
        frame.notices.refs.handleGraphEvent event available,
        frame.notices.records.handleGraphEvent event matching available,
        frame.notices.support.handleGraphEvent frame.started frame.tasks event matching
          available
      ⟩,
      frame.started.handleGraphEvent event available,
      frame.tasks.handleGraphEvent event matching available
    ⟩,
    State.handleGraphEvent_groupNoticesLocated generated frame.notices.refs
      frame.notices.records frame.notices.support event matching available
  ⟩

/-- Notice provenance follows the state after internal enqueue effects are realized. -/
private theorem NoticeReplayFrame.dispatchGraphEvent {work queue}
    (frame : NoticeReplayFrame work queue) (generated : ExecutedWork work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : NoticeReplayFrame work (queue.dispatchGraphEvent event available).1
      ∧ ∀ output ∈ (queue.dispatchGraphEvent event available).2,
          output.GroupNoticesLocated work := by
  have next := frame.handleGraphEvent generated event matching available
  exact ⟨⟨⟨next.1.notices.refs, next.1.notices.records,
    ⟨next.1.notices.support.contents, next.1.notices.support.roots⟩⟩,
    next.1.started, next.1.tasks⟩, next.2⟩

/-- Eventwise replay certifies notices before and after every source settlement.
Witness: list induction through the actual handler results, not an admitted-history premise.
-/
private theorem NoticeReplayFrame.rawEventReplay {work queue}
    (frame : NoticeReplayFrame work queue) (generated : ExecutedWork work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : NoticeReplayFrame work (queue.rawEventReplay events available).1
      ∧ ∀ output ∈ (queue.rawEventReplay events available).2,
          output.GroupNoticesLocated work := by
  induction events generalizing queue with
  | nil => exact ⟨frame, by simp [State.rawEventReplay]⟩
  | cons event rest ih =>
      rw [State.rawEventReplay_cons _ _ _ available]
      obtain ⟨next, outputs⟩ := frame.dispatchGraphEvent generated event
        (matching event List.mem_cons_self) available
      obtain ⟨final, later⟩ := ih next
        (fun child member => matching child (List.mem_cons_of_mem _ member))
      exact ⟨final, fun output member =>
        (List.mem_append.mp member).elim (outputs output) (later output)⟩

/-- A whole host batch keeps the provenance frame, including optional termination.
Witness: eventwise replay supplies notices; changing the terminal flag adds no descriptor.
-/
theorem NoticeReplayFrame.handleGraphEvents {work queue}
    (frame : NoticeReplayFrame work queue) (generated : ExecutedWork work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : NoticeReplayFrame work (queue.handleGraphEvents events).1
      ∧ ∀ output ∈ (queue.handleGraphEvents events).2,
          output.GroupNoticesLocated work := by
  rw [State.handleGraphEvents_eq_rawEventReplay queue events]
  split
  · exact ⟨frame, by simp⟩
  · obtain ⟨next, outputs⟩ := frame.rawEventReplay generated events matching
      (GraphEvent.availableFailures events)
    dsimp only
    split
    · refine ⟨⟨⟨next.notices.refs, next.notices.records,
        ⟨next.notices.support.contents, next.notices.support.roots⟩⟩,
        next.started, next.tasks⟩, ?_⟩
      intro output member
      rcases List.mem_append.mp member with old | terminal
      · exact outputs output old
      · obtain rfl := List.mem_singleton.mp terminal
        trivial
    · exact ⟨next, outputs⟩

/-- Matching generated replay retains the metadata needed by all later notice boundaries.
Witness: initialize the independently proved state facts and preserve the joint frame
through actual handlers. The raw output is not assumed to satisfy scheduler admission.
-/
theorem ExecutedWork.replay_noticeMetadata {work before}
    (generated : ExecutedWork work) (prior : ∀ event ∈ before, event.MatchesWork work)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      current.GroupRefsUnique
      ∧ current.GroupNodesMatchWork work
      ∧ current.GroupRefSupport
          (fun ref =>
            ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  have initial : NoticeReplayFrame work (State.initialize (Work.fromExecution work)) :=
    ⟨⟨createWorkQueue_groupRefsUnique _, createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_fromSpec_groupRefSupport work⟩,
      createWorkQueue_startedTasksRegistered _,
      createWorkQueue_fromSpec_registeredTasksMatch work⟩
  have replayed := (initial.rawEventReplay generated before prior).1.notices
  rw [State.rawEventReplay_state] at replayed
  exact ⟨replayed.refs, replayed.records, replayed.support⟩

/-- Matching replay supplies the full notice frame after task-success child preparation.
Witness: initialization and actual handler replay retain metadata and contributor support;
the incoming matching event supplies new child records and exact task owners. The task
lookup and healthy guard are unnecessary for this prepared-state metadata alone.
-/
theorem ExecutedWork.taskSuccess_prepared_noticeMetadata {work before occurrence result}
    (generated : ExecutedWork work)
    (prior : ∀ event ∈ before, event.MatchesWork work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (incoming : TaskNode)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      prepared.GroupRefsUnique
      ∧ prepared.GroupNodesMatchWork work
      ∧ prepared.GroupRefSupport
          (fun ref =>
            ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  obtain ⟨refs, records, support⟩ := generated.replay_noticeMetadata prior
  let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
  let stored := current.putTaskNode { incoming with value := some result.value }
  have frame : NoticeFrame work stored :=
    ⟨refs, records, ⟨support.contents, support.roots⟩⟩
  have prepared := frame.maybeIntegrateWork result.work
    (fun _ member => matching.taskChildGroups_recordAt member)
    (by
      intro task member group owner
      obtain ⟨address, payload, occurrenceEq, located⟩ := matching.childTask_producer member
      have known : TaskMatches work task :=
        ⟨⟨address, payload, some occurrence, occurrenceEq, located⟩,
          matching.childTask_groupsExact member⟩
      exact known.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩))
    (some occurrence)
  exact ⟨prepared.refs, prepared.records, prepared.support⟩

/-- The actual successful owner fold supplies notice metadata to its subsequent drain.
Witness: preserve the prepared frame through the single pass, then activate its proven
contributor frontier. No scheduler-admission or notice-freshness premise is needed.
-/
theorem ExecutedWork.taskSuccess_drain_noticeMetadata {work before occurrence result}
    (generated : ExecutedWork work) (prior : ∀ event ∈ before, event.MatchesWork work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (incoming : TaskNode)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := (released.1.startNewWork released.2.2).1
      active.GroupRefsUnique
      ∧ active.GroupNodesMatchWork work
      ∧ active.GroupRefSupport
          (fun ref =>
            ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  obtain ⟨refs, records, support⟩ :=
    generated.taskSuccess_prepared_noticeMetadata prior matching incoming
  obtain ⟨frame, _, released⟩ :=
    NoticeFrame.successGroupFold ⟨refs, records, support⟩ generated incoming.task.groups
  have active := frame.startNewWork _ released
  exact ⟨active.refs, active.records, active.support⟩

/-- Item integration supplies notice metadata before the handler's recursive drain.
Witness: each matching item's pruning frontier contains actual contributors, and its
activation preserves the frame for the next item. No item-publication proof is assumed.
-/
theorem ExecutedWork.streamItems_prepared_noticeMetadata {work before stream items}
    (generated : ExecutedWork work) (prior : ∀ event ∈ before, event.MatchesWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared := current.preparedStreamItems items
      prepared.GroupRefsUnique
      ∧ prepared.GroupNodesMatchWork work
      ∧ prepared.GroupRefSupport
          (fun ref =>
            ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
  obtain ⟨refs, records, support⟩ := generated.replay_noticeMetadata prior
  have frame := State.preparedStreamItems_preserves (NoticeFrame work)
    ⟨refs, records, support⟩ items [] (fun _ item member frame =>
      (frame.integrateStreamItem generated matching member).1)
  exact ⟨frame.refs, frame.records, frame.support⟩

/-- Every normalized group-notice descriptor denotes a real node of the fixed work.
The predicate deliberately says nothing yet about freshness or causal readiness.
-/
def GroupNoticesLocated (work : Execution.Work) : Execution.WorkQueueEvent → Prop
  | .groupSuccess _ groups _ | .streamValues _ _ groups _ =>
      ∀ group ∈ groups,
        ∃ dependencies producer, NodeAt work group .group dependencies producer
  | _ => True

/-- Publisher normalization copies group notices without remapping their descriptors.
Witness: event case analysis; shared-value owner selection cannot introduce a notice.
-/
theorem IncrementalPublisher.normalizeBatch_groupNoticesLocated {work events}
    (publisher : IncrementalPublisher)
    (known : ∀ event ∈ events, event.GroupNoticesLocated work)
    : ∀ output ∈ (publisher.normalizeBatch events).2,
        GroupNoticesLocated work output := by
  have one (current : IncrementalPublisher) (event : WorkQueueEvent)
      (located : event.GroupNoticesLocated work)
      : ∀ output ∈ (current.handleWorkQueueEvent event).2,
          GroupNoticesLocated work output := by
    cases event <;> simp_all [IncrementalPublisher.handleWorkQueueEvent,
      WorkQueueEvent.GroupNoticesLocated, GroupNoticesLocated]
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      intro output member
      exact (List.mem_append.mp member).elim
        (one publisher event (known event List.mem_cons_self) output)
        (ih _ (fun next member => known next (List.mem_cons_of_mem _ member)) output)

/-- Every group announced by actual normalized replay has a real contributing work node.
Witness: initialize the independent ref/record/support and task-registry invariants,
replay matched inputs, and preserve notice descriptors through publisher normalization.
No output admission, causal health, start discipline, or notice freshness is assumed.
-/
theorem createWorkQueue_runNormalized_groupNoticesLocated {work : Execution.Work}
    (generated : ExecutedWork work) {inputs : List (List GraphEvent)}
    (valid : ValidGraphEvents work inputs.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten,
        GroupNoticesLocated work event := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (frame : NoticeReplayFrame work acc.1)
      (notices : ∀ event ∈ acc.2.2.flatten, GroupNoticesLocated work event)
      (matching : ∀ event ∈ more.flatten, event.MatchesWork work)
      : ∀ event ∈ (more.foldl normalizedStep acc).2.2.flatten,
          GroupNoticesLocated work event := by
    induction more generalizing acc with
    | nil => exact notices
    | cons batch rest ih =>
        obtain ⟨next, emitted⟩ := frame.handleGraphEvents generated batch
          (fun event member => matching event (List.mem_append_left _ member))
        apply ih
        · rw [normalizedStep_queue]
          exact next
        · rw [normalizedStep_flatten]
          intro event member
          exact (List.mem_append.mp member).elim (notices event)
            (acc.2.1.normalizeBatch_groupNoticesLocated emitted event)
        · exact fun event member => matching event (List.mem_append_right _ member)
  apply loop inputs (_, _, [])
  · exact ⟨⟨createWorkQueue_groupRefsUnique _, createWorkQueue_groupNodesMatchWork work,
      createWorkQueue_fromSpec_groupRefSupport work⟩,
      createWorkQueue_startedTasksRegistered _,
      createWorkQueue_fromSpec_registeredTasksMatch work⟩
  · simp
  · exact fun _ member => valid.eachMatches member

/-- Atomic splitting retains group-notice provenance, including final item carriers.
Witness: earlier item atoms carry no notices; only the last retains the original list.
-/
theorem publicationAtoms_groupNoticesLocated {work} (event : Execution.WorkQueueEvent)
    (known : GroupNoticesLocated work event)
    : ∀ atom ∈ publicationAtoms event, GroupNoticesLocated work atom := by
  cases event with
  | groupValues group values => simp [publicationAtoms, GroupNoticesLocated]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms]
      | case2 =>
          simpa [publicationAtoms, streamPublicationAtoms, GroupNoticesLocated] using known
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, GroupNoticesLocated] using ih known
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simpa [publicationAtoms] using known

/-- Every group notice in the actual atomic history has contributor provenance.
Witness: compose actual normalized replay with notice-preserving atomization. This does
not select a matching or failure inventory and therefore applies to the common witness.
-/
theorem createWorkQueue_runNormalized_atomicGroupNoticesLocated {work : Execution.Work}
    (generated : ExecutedWork work) {inputs : List (List GraphEvent)}
    (valid : ValidGraphEvents work inputs.flatten)
    : ∀ event ∈
        (((State.initialize (Work.fromExecution work)).runNormalized
            inputs).2.flatten.flatMap
          publicationAtoms),
        GroupNoticesLocated work event := by
  intro event member
  obtain ⟨original, emitted, atom⟩ := List.mem_flatMap.mp member
  exact publicationAtoms_groupNoticesLocated original
    (createWorkQueue_runNormalized_groupNoticesLocated generated valid original emitted) event atom

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
