import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverageCore
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskCatalogue

/-! Derived declaration contexts accompany registry coverage through executable replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics
open DeclarationCoverage
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

/-- A certified chunk's immediate parent lies in its retained context or candidate refs. -/
theorem DeclarationCoverage.WorkCertificate.parentRefs {work known incoming}
    (certificate : WorkCertificate work known incoming)
    : ∀ group ∈ incoming.groups,
        ∀ parent,
          group.parent = some parent
          → parent ∈ known ++ incoming.groups.map (fun group => group.node.ref) := by
  intro group member parent parentEq
  rcases certificate.parents group member parent parentEq with old | fresh
  · exact List.mem_append_left _ old
  · obtain ⟨candidate, included, same⟩ := fresh
    exact List.mem_append_right _ (List.mem_map.mpr ⟨candidate, included, same⟩)

/-- Proof evidence for registrations and the future child contexts of permanent tasks.
The source certificate is derived from pure execution. No field is executable state or
an extra requirement on host source admission.
-/
structure State.RegistrationFrame (queue : State) (work : Execution.Work) : Prop where
  source : Certified [] work
  live : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  children : ∀ task ∈ queue.tasks, TaskChildrenCertified work queue.registeredGroups task
  started : queue.StartedTasksRegistered

/-- Retaining tasks and prior registrations retains their child-context evidence. -/
theorem State.RegistrationFrame.retain {queue next : State} {work : Execution.Work}
    (frame : queue.RegistrationFrame work)
    (live : next.LiveGroupsRegistered) (tasks : next.TaskGroupsRegistered)
    (started : next.StartedTasksRegistered)
    (retained : next.tasks.Subset queue.tasks)
    (registered : queue.registeredGroups.Subset next.registeredGroups)
    : next.RegistrationFrame work := by
  refine ⟨frame.source, live, tasks, ?_, started⟩
  intro task member
  exact (frame.children task (retained member)).mono registered

/-- Group replacement retains all permanent declaration contexts. -/
theorem State.RegistrationFrame.putGroupNode {queue work}
    (frame : State.RegistrationFrame queue work) (updated : GroupNode)
    (registered : updated.group.node.ref ∈ queue.registeredGroups)
    : (queue.putGroupNode updated).RegistrationFrame work :=
  ⟨
    frame.source,
    frame.live.putGroupNode updated registered,
    frame.tasks,
    frame.children,
    frame.started.putGroupNode updated
  ⟩

/-- Updating a started computation retains its permanent task's declaration context. -/
theorem State.RegistrationFrame.putTaskNode {queue work}
    (frame : State.RegistrationFrame queue work) (updated : TaskNode)
    (registered : updated.task ∈ queue.tasks)
    : (queue.putTaskNode updated).RegistrationFrame work :=
  ⟨
    frame.source,
    frame.live,
    frame.tasks,
    frame.children,
    frame.started.putTaskNode updated registered
  ⟩

/-- Cache availability changes no permanent registration or task context. -/
theorem State.RegistrationFrame.cacheTaskFailures {queue work}
    (frame : State.RegistrationFrame queue work) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).RegistrationFrame work := by
  have coverage := queue.cacheTaskFailures_registration frame.live frame.tasks available
  apply frame.retain coverage.1 coverage.2 (frame.started.cacheTaskFailures available)
  · rw [State.cacheTaskFailures_tasks]; exact fun _ member => member
  · rw [State.cacheTaskFailures_registeredGroups]; exact fun _ member => member

/-- Integration records earlier or fresh task owners and certifies all future children. -/
theorem State.RegistrationFrame.maybeIntegrateWork {queue work}
    (frame : State.RegistrationFrame queue work) (incoming : Work)
    (certificate : WorkCertificate work queue.registeredGroups incoming)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork incoming producer).1.RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.maybeIntegrateWork incoming producer).1.registeredGroups := by
  have coverage := queue.maybeIntegrateWork_registration frame.live frame.tasks incoming
    certificate.contributors producer
  refine ⟨⟨frame.source, coverage.1, coverage.2.1, ?_,
    frame.started.maybeIntegrateWork incoming producer⟩, coverage.2.2⟩
  intro task member
  rw [State.maybeIntegrateWork_tasks_append] at member
  rcases List.mem_append.mp member with old | fresh
  · exact (frame.children task old).mono coverage.2.2
  · exact (certificate.children task fresh).mono
      (queue.maybeIntegrateWork_registrationContext frame.live incoming producer)

/-- Empty-group pruning keeps the declaration history and permanent task contexts. -/
theorem State.RegistrationFrame.pruneEmptyGroups {queue work}
    (frame : State.RegistrationFrame queue work) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.RegistrationFrame work := by
  have coverage := queue.pruneEmptyGroups_registration frame.live frame.tasks groups
  apply frame.retain coverage.1 coverage.2.1 (frame.started.pruneEmptyGroups groups)
  · rw [State.pruneEmptyGroups_tasks]; exact fun _ member => member
  · rw [coverage.2.2]; exact fun _ member => member

/-- Starting roots keeps declarations even when cached rejection removes live owners. -/
theorem State.RegistrationFrame.startNewWork {queue work}
    (frame : State.RegistrationFrame queue work) (incoming : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork incoming available).1.RegistrationFrame work := by
  have coverage := queue.startNewWork_registration frame.live frame.tasks incoming available
  apply frame.retain coverage.1 coverage.2 (frame.started.startNewWork incoming available)
  · rw [State.startNewWork_tasks]; exact fun _ member => member
  · rw [State.startNewWork_registeredGroups]; exact fun _ member => member

/-- Successful release removes live task nodes and keeps permanent contexts. -/
theorem State.RegistrationFrame.finishGroupSuccess {queue work}
    (frame : State.RegistrationFrame queue work) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RegistrationFrame work := by
  have coverage := queue.finishGroupSuccess_registration frame.live frame.tasks group
  apply frame.retain coverage.1 coverage.2.1 (frame.started.finishGroupSuccess group)
  · rw [State.finishGroupSuccess_tasks]; exact fun _ member => member
  · rw [coverage.2.2]; exact fun _ member => member

/-- Recursive release retains permanent registration contexts. -/
theorem State.RegistrationFrame.drainReadyGroups {queue work}
    (frame : State.RegistrationFrame queue work)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.RegistrationFrame work :=
  State.drainReadyGroups_preserves (fun current => current.RegistrationFrame work)
    (fun _ group prior _ _ _ => (prior.finishGroupSuccess group).startNewWork _ available)
    frame

/-- Failure cleanup retains the full declaration history of permanent tasks. -/
theorem State.RegistrationFrame.taskFailure {queue work}
    (frame : State.RegistrationFrame queue work) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.RegistrationFrame work := by
  have coverage := queue.taskFailure_registration frame.live frame.tasks occurrence errors
  apply frame.retain coverage.1 coverage.2.1 (frame.started.taskFailure occurrence errors)
  · rw [State.taskFailure_tasks]; exact fun _ member => member
  · rw [coverage.2.2]; exact fun _ member => member

/-- A contributor settlement preserves contexts and the exact permanent registry. -/
theorem State.RegistrationFrame.settleGroup {queue work}
    (frame : State.RegistrationFrame queue work) (outputs : List WorkQueueEvent)
    (released : NewWork) (group : Execution.DeliveryNode)
    : (successGroupStep (queue, outputs, released) group).1.RegistrationFrame work
      ∧ (successGroupStep (queue, outputs, released) group).1.registeredGroups
        = queue.registeredGroups := by
  dsimp only [successGroupStep]
  split
  · exact ⟨frame, rfl⟩
  · rename_i node found
    have updated := frame.putGroupNode { node with pending := node.pending - 1 }
      (frame.live node (List.mem_of_find?_eq_some found))
    split
    · exact ⟨updated.finishGroupSuccess _,
        (State.finishGroupSuccess_registration updated.live updated.tasks _).2.2⟩
    · exact ⟨updated, rfl⟩

/-- A matched successful producer supplies children with its actual retained context. -/
theorem State.RegistrationFrame.taskSuccess {queue work}
    (frame : State.RegistrationFrame queue work) (occurrence : Occurrence)
    (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.taskSuccess occurrence result available).1.registeredGroups := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      exact ⟨frame, fun _ member => member⟩
  | some node =>
      have registered := frame.started node (List.mem_of_find?_eq_some found)
      have same : node.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : TaskNode =>
          candidate.task.occurrence == occurrence) found)
      have supplied := (frame.children node.task registered).sourceChild same matching
      have stored := frame.putTaskNode { node with value := some result.value } registered
      have integrated := stored.maybeIntegrateWork result.work supplied (some occurrence)
      let property (acc : State × List WorkQueueEvent × NewWork) :=
        acc.1.RegistrationFrame work ∧ queue.registeredGroups.Subset acc.1.registeredGroups
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List WorkQueueEvent × NewWork) (prior : property acc)
          : property (groups.foldl successGroupStep acc) := by
        induction groups generalizing acc with
        | nil => exact prior
        | cons group rest ih =>
            have next := prior.1.settleGroup acc.2.1 acc.2.2 group
            exact ih _ ⟨next.1, next.2 ▸ prior.2⟩
      let initial := ((queue.putTaskNode { node with value := some result.value }
        ).maybeIntegrateWork result.work (some occurrence)).1
      have folded := loop node.task.groups (initial, [], {}) integrated
      let finished := node.task.groups.foldl successGroupStep (initial, [], {})
      have started := folded.1.startNewWork finished.2.2 available
      have drained := started.drainReadyGroups available
      rw [queue.taskSuccess_eq occurrence result node found available]
      refine ⟨drained, ?_⟩
      rw [(State.drainReadyGroups_registration started.live started.tasks available).2.2,
        State.startNewWork_registeredGroups]
      exact folded.2

/-- One matched item establishes its fresh declarations before starting child tasks. -/
theorem State.RegistrationFrame.integrateStreamItem {queue work stream items}
    (frame : State.RegistrationFrame queue work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.integrateStreamItem item available).registeredGroups := by
  have supplied := frame.source.sourceStreamItem matching member queue.registeredGroups
  have integrated := frame.maybeIntegrateWork item.work supplied
  have pruned := integrated.1.pruneEmptyGroups (queue.maybeIntegrateWork item.work).2.newGroups
  let integratedWork := queue.maybeIntegrateWork item.work
  let prepared := integratedWork.1.pruneEmptyGroups integratedWork.2.newGroups
  have started := pruned.startNewWork { integratedWork.2 with newGroups := prepared.2 } available
  refine ⟨started, ?_⟩
  unfold State.integrateStreamItem
  rw [State.startNewWork_registeredGroups,
    (State.pruneEmptyGroups_registration integrated.1.live integrated.1.tasks _).2.2]
  exact integrated.2

/-- A matched item batch extends registrations in its actual integration order. -/
theorem State.RegistrationFrame.streamItems {queue work stream items}
    (frame : State.RegistrationFrame queue work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.streamItems stream items available).1.registeredGroups := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List Execution.StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) := pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  let property (current : State) := current.RegistrationFrame work
    ∧ queue.registeredGroups.Subset current.registeredGroups
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List Execution.StreamItemValue × List GroupFailureEvent)
      (prior : property acc.1) : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        have next := prior.1.integrateStreamItem matching (included List.mem_cons_self) available
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (step acc item) ⟨next.1, prior.2.trans next.2⟩
  unfold State.streamItems
  split
  · exact ⟨frame, fun _ member => member⟩
  · have folded := loop items (fun _ member => member) (queue, [], [], [], [])
      ⟨frame, fun _ member => member⟩
    exact ⟨folded.1.drainReadyGroups available,
      (State.drainReadyGroups_registration folded.1.live folded.1.tasks available).2.2 ▸ folded.2⟩

/-- A queued-notice update leaves registration evidence unchanged. -/
theorem State.RegistrationFrame.withGroupFailures {queue work}
    (frame : State.RegistrationFrame queue work) (notices : List GroupFailureEvent)
    : ({ queue with groupFailureEvents := notices }).RegistrationFrame work :=
  ⟨frame.source, frame.live, frame.tasks, frame.children, frame.started⟩

/-- The terminal control flag leaves registration evidence unchanged. -/
theorem State.RegistrationFrame.withTerminated {queue work}
    (frame : State.RegistrationFrame queue work) (terminal : Bool)
    : ({ queue with terminated := terminal }).RegistrationFrame work :=
  ⟨frame.source, frame.live, frame.tasks, frame.children, frame.started⟩

/-- A matched FIFO outcome preserves contexts and every prior registration. -/
theorem State.RegistrationFrame.handleGraphEvent {queue work}
    (frame : State.RegistrationFrame queue work) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.handleGraphEvent event available).1.registeredGroups := by
  have cached := frame.cacheTaskFailures available
  have output : (queue.handleGraphEvent event available).1.RegistrationFrame work
      ∧ (queue.cacheTaskFailures available).registeredGroups.Subset
          (queue.handleGraphEvent event available).1.registeredGroups := by
    cases event with
    | taskSuccess occurrence result =>
        exact cached.taskSuccess occurrence result matching available
    | taskFailure occurrence errors =>
        exact ⟨cached.taskFailure occurrence errors,
          (State.taskFailure_registration cached.live cached.tasks occurrence errors).2.2 ▸
            (fun _ member => member)⟩
    | streamItems stream items => exact cached.streamItems matching available
    | groupFailure failure =>
        simp only [State.handleGraphEvent, State.groupFailure]
        split
        · exact ⟨cached, fun _ member => member⟩
        · split
          · exact ⟨cached.withGroupFailures _, fun _ member => member⟩
          · exact ⟨cached, fun _ member => member⟩
    | streamSuccess stream =>
        simp only [State.handleGraphEvent, State.streamSuccess]
        split
        · exact ⟨⟨cached.source, cached.live, cached.tasks, cached.children, cached.started⟩,
            fun _ member => member⟩
        · exact ⟨cached, fun _ member => member⟩
    | streamFailure stream errors =>
        simp only [State.handleGraphEvent, State.streamFailure]
        split
        · exact ⟨⟨cached.source, cached.live, cached.tasks, cached.children, cached.started⟩,
            fun _ member => member⟩
        · exact ⟨cached, fun _ member => member⟩
  exact ⟨output.1, (queue.cacheTaskFailures_registeredGroups available) ▸ output.2⟩

/-- Realizing enqueue effects retains the frame, including the notice FIFO. -/
theorem State.RegistrationFrame.dispatchGraphEvent {queue work}
    (frame : State.RegistrationFrame queue work) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.dispatchGraphEvent event available).1.registeredGroups := by
  have next := frame.handleGraphEvent event matching available
  exact ⟨next.1.withGroupFailures _, next.2⟩

/-- Fixed-availability replay threads the derived contexts through actual dispatch. -/
theorem State.RegistrationFrame.replayGraphEvents {queue work}
    (frame : State.RegistrationFrame queue work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.replayGraphEvents events available).registeredGroups := by
  induction events generalizing queue with
  | nil => exact ⟨frame, fun _ member => member⟩
  | cons event rest ih =>
      have next := frame.dispatchGraphEvent event (matching event List.mem_cons_self) available
      have later := ih next.1 (fun event member => matching event (List.mem_cons_of_mem _ member))
      exact ⟨later.1, next.2.trans later.2⟩

/-- Batch termination adds no registration premise and retains pending FIFO evidence. -/
theorem State.RegistrationFrame.handleGraphEvents {queue work}
    (frame : State.RegistrationFrame queue work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.handleGraphEvents events).1.registeredGroups := by
  cases running : queue.terminated with
  | true =>
      simpa only [State.handleGraphEvents, running, ite_true]
        using (show queue.RegistrationFrame work
                    ∧ queue.registeredGroups.Subset queue.registeredGroups from ⟨
                frame,
                fun _ member => member
              ⟩)
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      have replayed := frame.replayGraphEvents events matching (GraphEvent.availableFailures events)
      rw [same]
      exact ⟨replayed.1.withTerminated terminal, replayed.2⟩

/-- Batch-aware replay preserves declaration contexts without flattening availability. -/
theorem State.RegistrationFrame.runNormalized {queue work}
    (frame : State.RegistrationFrame queue work) (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : (queue.runNormalized batches).1.RegistrationFrame work
      ∧ queue.registeredGroups.Subset
          (queue.runNormalized batches).1.registeredGroups := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue with
  | nil => exact ⟨frame, fun _ member => member⟩
  | cons batch rest ih =>
      have next := frame.handleGraphEvents batch (matching batch List.mem_cons_self)
      have later := ih next.1 (fun batch member => matching batch (List.mem_cons_of_mem _ member))
      exact ⟨later.1, next.2.trans later.2⟩

/-- Enqueueing a notice changes no registration or child-context evidence. -/
theorem State.RegistrationFrame.enqueueGroupFailures {queue work}
    (frame : State.RegistrationFrame queue work) (failures : List GroupFailureEvent)
    : (queue.enqueueGroupFailures failures).RegistrationFrame work :=
  ⟨frame.source, frame.live, frame.tasks, frame.children, frame.started⟩

/-- Initial response metadata does not affect the registration certificate. -/
theorem State.RegistrationFrame.withInitialNotices {queue work}
    (frame : State.RegistrationFrame queue work)
    (groups streams : List Execution.DeliveryNode)
    : ({
        queue with
          initialGroups := groups, initialStreams := streams
      }).RegistrationFrame
        work :=
  ⟨frame.source, frame.live, frame.tasks, frame.children, frame.started⟩

/-- Initialization derives all registration evidence from the pure work certificate. -/
theorem State.initialize_registrationFrame {work : Execution.Work}
    (certified : Certified [] work)
    : (State.initialize (Work.fromExecution work)).RegistrationFrame work := by
  have empty : ({} : State).RegistrationFrame work := by
    refine ⟨certified, ?_, ?_, ?_, ?_⟩ <;> intro node member <;> cases member
  have supplied := certified.lower (Located.root (root := work))
  let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let prepared := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have started := ((empty.maybeIntegrateWork (Work.fromExecution work) supplied).1.pruneEmptyGroups
    integrated.2.newGroups).startNewWork { integrated.2 with newGroups := prepared.2 }
  exact (started.enqueueGroupFailures
          (prepared.1.startNewWork
            { integrated.2 with newGroups := prepared.2 }).2).withInitialNotices
    prepared.2 integrated.2.newStreams

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
