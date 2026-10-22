import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrainOutput
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupStartup

/-! Concrete cancellation markers retain the positive completion that caused cleanup. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Report origins propagate through full registration ancestry
-----------------------------------------------------------------------------------------

/-- A report covering a parent also covers its child's full ancestor-ref chain.
Witness: a direct parent report becomes an ancestor report; an earlier ancestor remains
in the child's transitive dependency list. This is ref-based provenance, not path coverage.
-/
theorem GroupFailureReported.inherit
    {work events child dependencies parent ancestors}
    (generated : ExecutedWork work)
    (childKnown : GroupRecordAt work child dependencies)
    (parentKnown : GroupRecordAt work parent ancestors)
    (above : parent.ref ∈ dependencies)
    (reported : GroupFailureReported events parent ancestors)
    : GroupFailureReported events child dependencies := by
  obtain ⟨reporter, errors, positive, emitted, same | earlier⟩ := reported
  · exact ⟨reporter, errors, positive, emitted, Or.inr (same ▸ above)⟩
  · exact ⟨reporter, errors, positive, emitted,
      Or.inr (generated.groupRecordAncestors_trans childKnown parentKnown above earlier)⟩

/-- Every concrete cancellation marker has an actual positive completion at the same
group or one of its full registration ancestors. `events` is a supplied completion inventory;
startup and drain lemmas include queued notices before actual batch forwarding. `work`
supplies record provenance, including taskless ancestor records.
This is an internal invariant to prove, not a public source or queue-contract premise.
-/
def State.CancelledRecordsReported (queue : State) (work : Execution.Work)
    (events : List Execution.WorkQueueEvent)
    : Prop :=
  ∀ node dependencies,
    GroupRecordAt work node dependencies
    → node.ref ∈ queue.cancelledGroups
    → GroupFailureReported events node dependencies

/-- Extending the output prefix preserves all previously justified cancellation markers.
Witness: every retained report remains an actual event in the extended output.
-/
theorem State.CancelledRecordsReported.append {queue : State} {work events}
    (reported : queue.CancelledRecordsReported work events)
    (tail : List Execution.WorkQueueEvent)
    : queue.CancelledRecordsReported work (events ++ tail) :=
  fun node dependencies known member =>
    (reported node dependencies known member).append tail

/-- Enlarging the supplied report inventory retains each cancellation explanation.
Witness: preserve the exact positive completion and its same-or-ancestor relationship.
-/
theorem State.CancelledRecordsReported.mono {queue : State} {work events more}
    (reported : queue.CancelledRecordsReported work events)
    (included : events.Subset more)
    : queue.CancelledRecordsReported work more := by
  intro node dependencies known cancelled
  obtain ⟨reporter, errors, positive, emitted, ancestry⟩ :=
    reported node dependencies known cancelled
  exact ⟨reporter, errors, positive, included emitted, ancestry⟩

/-- A state change preserving cancellation refs preserves their report explanations. -/
theorem State.CancelledRecordsReported.of_sameCancelled {queue next : State} {work events}
    (reported : queue.CancelledRecordsReported work events)
    (same : next.cancelledGroups = queue.cancelledGroups)
    : next.CancelledRecordsReported work events := by
  intro node dependencies known cancelled
  exact reported node dependencies known (same ▸ cancelled)

/-- Initial concrete state has no cancellation markers to report.
Witness: initialization's empty cancellation registry, even for arbitrary raw work.
-/
theorem createWorkQueue_cancelledRecordsReported (initialWork : Work)
    (work : Execution.Work) (events : List Execution.WorkQueueEvent)
    : (State.initialize initialWork).CancelledRecordsReported work events := by
  intro node dependencies known member
  rw [createWorkQueue_cancelledGroups_empty] at member
  cases member

-----------------------------------------------------------------------------------------
-- Late refused registration inherits an existing ancestor completion
-----------------------------------------------------------------------------------------

/-- Registering a child below a cancelled parent retains actual report provenance.
Witness: refusal adds only the child marker; the parent's record and completion propagate
through full generated ancestry. Successful or repeated registration adds no marker.
-/
theorem State.CancelledRecordsReported.addGroup {queue : State} {work events}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (group : Group)
    (matching
      : ∃ dependencies,
          GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head?)
    : (queue.addGroup group).CancelledRecordsReported work events := by
  unfold State.addGroup
  split
  · exact reported
  · split
    · exact reported
    · rename_i parent parentEq
      split
      · split
        · rename_i blocked
          intro node dependencies known member
          rcases List.mem_append.mp member with old | added
          · exact reported node dependencies known old
          · have same : node.ref = group.node.ref := List.mem_singleton.mp added
            obtain ⟨groupDependencies, groupKnown, canonicalParent⟩ := matching
            obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
            have equalDependencies : dependencies = groupDependencies := by
              rw [canonical _ _ known, canonical _ _ groupKnown, same]
            have cancelled : parent ∈ queue.cancelledGroups := by simpa using blocked
            have head : dependencies.head? = some parent :=
              equalDependencies.symm ▸ (canonicalParent.symm.trans parentEq)
            cases dependencies with
            | nil => cases head
            | cons ref ancestors =>
                have sameParent : ref = parent := Option.some.inj head
                subst ref
                obtain ⟨parentNode, parentRef, parentKnown⟩ := known.parent
                exact (reported parentNode ancestors parentKnown
                        (parentRef.symm ▸ cancelled)).inherit
                  generated known parentKnown (by simp [parentRef])
        · exact reported
      · exact reported

/-- A complete registration batch preserves report provenance in any candidate order.
Witness: thread refused-child inheritance through recursive parent-first installation.
No notice is emitted for a refused child.
-/
theorem State.CancelledRecordsReported.addGroups {queue : State} {work events}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (groups : List Group)
    (matching
      : ∀ group ∈ groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    : (queue.addGroups groups).1.CancelledRecordsReported work events := by
  exact State.addGroups_preserves (fun current => current.CancelledRecordsReported work events)
    groups (fun _ group member prior => prior.addGroup generated group (matching group member))
    queue reported

/-- Integrating work preserves cancellation reports through its group-registration stage.
Witness: later task and stream installation leave cancellation markers unchanged.
-/
theorem State.CancelledRecordsReported.maybeIntegrateWork {queue : State} {work events}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (newWork : Work) (parentTask : Option Occurrence)
    (matching
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    : (queue.maybeIntegrateWork newWork parentTask).1.CancelledRecordsReported work
        events := by
  intro node dependencies known member
  rw [State.maybeIntegrateWork_cancelledGroups queue newWork parentTask] at member
  exact reported.addGroups generated newWork.groups matching node dependencies known member

-----------------------------------------------------------------------------------------
-- Failure cleanup records only descendants of the actual positive-error completion
-----------------------------------------------------------------------------------------

/-- Removing a failed group's subtree gives every new marker the same actual report.
Witness: collector provenance supplies a stored live path from the closing root; generated
canonical ancestry identifies that root as the removed record or one of its ancestors.
The original collector's finite budget does not affect this provenance direction.
-/
theorem State.CancelledRecordsReported.removeGroup
    {queue : State} {work : Execution.Work} {events : List Execution.WorkQueueEvent}
    {parents : NodeRef → NodeRefs} {reporter : Execution.DeliveryNode} {errors : Nat}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (positive : 0 < errors) (emitted : .groupFailure reporter errors ∈ events)
    : (queue.removeGroup reporter.ref).CancelledRecordsReported work events := by
  intro node dependencies known member
  change node.ref ∈ queue.cancelledGroups ++ State.removeGroup.collect
    (queue.groupNodes.length + 1) queue [reporter.ref] [] at member
  rcases List.mem_append.mp member with old | added
  · exact reported node dependencies known old
  · rcases State.removeGroup_collect_provenance (queue.groupNodes.length + 1) queue
      [reporter.ref] [] added with impossible | ⟨root, singleton, path⟩
    · cases impossible
    · have same : root = reporter.ref := List.mem_singleton.mp singleton
      have ancestor := path.ancestor_or_self generated records links canonical known rfl
      exact ⟨reporter, errors, positive, emitted, same ▸ ancestor⟩

/-- Successful group closure preserves all report origins and appends its actual outputs.
Witness: successful retirement creates no cancellation marker; previous reports persist.
-/
theorem State.CancelledRecordsReported.finishGroupSuccess {queue : State} {work events}
    (reported : queue.CancelledRecordsReported work events) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.CancelledRecordsReported work
        (events ++ (queue.finishGroupSuccess group).2.1) := by
  intro node dependencies known member
  rw [State.finishGroupSuccess_cancelledGroups] at member
  exact (reported node dependencies known member).append _

/-- Failed closure records its own emitted completion as the origin of subtree cleanup.
Witness: the executable handler emits exactly the supplied positive-error completion;
collector ancestry then propagates it to every newly recorded cancellation marker.
-/
theorem State.CancelledRecordsReported.finishGroupFailure
    {queue : State} {work : Execution.Work} {events : List Execution.WorkQueueEvent}
    {parents : NodeRef → NodeRefs}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (group : GroupNode) (errors : Nat) (positive : 0 < errors)
    : (queue.finishGroupFailure group errors).1.CancelledRecordsReported work
        (events
          ++ [.groupFailure (queue.finishGroupFailure group errors).2.group
                (queue.finishGroupFailure group errors).2.errors]) := by
  exact (reported.append [.groupFailure group.group.node errors]).removeGroup
    generated records links canonical positive (by simp)

/-- Starting one group accounts for new cancellation with its queued positive notice.
Witness: cache exposure and successful starts add no marker. Failed startup copies the
looked-up descriptor into one positive aggregate notice before removing its subtree.
-/
theorem State.CancelledRecordsReported.startGroup {queue : State} {work events parents}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (positive : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (ref : NodeRef) (available : List (Occurrence × Nat))
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors)
    : (queue.startGroup ref available).1.CancelledRecordsReported work
        (events
          ++ (queue.startGroup ref available).2.map
              (fun failure => .groupFailure failure.group failure.errors)) := by
  have cached := reported.of_sameCancelled (queue.cacheTaskFailures_cancelledGroups available)
  have cachedRecords := records.cacheTaskFailures available
  have cachedLinks : (queue.cacheTaskFailures available).ChildLinksCanonical parents := by
    intro node member child included
    rw [State.cacheTaskFailures_groupNodes] at member
    exact links node member child included
  cases found : (queue.cacheTaskFailures available).groupNode? ref with
  | none =>
      simpa only [State.startGroup, found, List.map_nil, List.append_nil] using cached
  | some node =>
      cases empty
            : (node.tasks.filterMap
                (fun task =>
                  ((queue.cacheTaskFailures available).taskNode? task).bind
                    (·.rejection))).isEmpty with
      | true =>
          have preserved := fold_projection State.cancelledGroups
            (fun current task => current.startTask task available)
            (fun current task => by unfold State.startTask; split; rfl; split <;> rfl)
            node.tasks (queue.cacheTaskFailures available)
          simpa only [State.startGroup, found, empty, ↓reduceIte, List.map_nil,
            List.append_nil]
            using cached.of_sameCancelled preserved
      | false =>
          have emitted : (⟨node.group.node, (node.tasks.filterMap
              (fun task =>
                ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection))).sum⟩
              : GroupFailureEvent) ∈ (queue.startGroup ref available).2 := by
            simp only [State.startGroup, found, empty, Bool.false_eq_true, ↓reduceIte]
            exact List.mem_cons_self
          have aggregate := queue.startGroup_failure_positive positive ref available licensed
            emitted
          simpa only [State.startGroup, found, empty, Bool.false_eq_true, ↓reduceIte,
            List.map_singleton]
            using cached.finishGroupFailure generated cachedRecords cachedLinks
              canonical node _ aggregate

/-- Activation accounts for cancellation using the returned batch-local startup notices.
Witness: each group start supplies its actual positive aggregate control; records, links
and task positivity survive the next start. Stream activation adds no cancellation marker.
-/
theorem State.CancelledRecordsReported.startNewWork {queue : State} {work events parents}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (positive : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (released : NewWork) (available : List (Occurrence × Nat) := [])
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors := by
      intro occurrence errors member; cases member)
    : (queue.startNewWork released available).1.CancelledRecordsReported work
        (events
          ++ (queue.startNewWork released available).2.map
              (fun failure => .groupFailure failure.group failure.errors)) := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (known : acc.1.GroupNodesMatchWork work) (edges : acc.1.ChildLinksCanonical parents)
      (counts : acc.1.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
      (prior : acc.1.CancelledRecordsReported work
        (events ++ acc.2.map (fun failure => .groupFailure failure.group failure.errors)))
      : (refs.foldl step acc).1.CancelledRecordsReported work
          (events ++ (refs.foldl step acc).2.map
            (fun failure => .groupFailure failure.group failure.errors)) := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        have nextKnown : (step acc ref).1.GroupNodesMatchWork work := by
          intro node member
          exact known node ((acc.1.startGroup_groupNodes_sublist ref available).subset member)
        have nextEdges : (step acc ref).1.ChildLinksCanonical parents := by
          intro node member child included
          exact edges node ((acc.1.startGroup_groupNodes_sublist ref available).subset member)
            child included
        have nextReported : (step acc ref).1.CancelledRecordsReported work
            (events ++ (step acc ref).2.map
              (fun failure => .groupFailure failure.group failure.errors)) := by
          simpa only [step, List.map_append, List.append_assoc]
            using prior.startGroup generated known edges canonical counts ref available
              licensed
        exact ih (step acc ref) nextKnown nextEdges
          (counts.startGroup ref available licensed) nextReported
  let initial : State := { queue with rootGroups :=
    queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref }
  let grouped := (released.newGroups.map Execution.DeliveryNode.ref).foldl step (initial, [])
  have groups :=
    loop (released.newGroups.map Execution.DeliveryNode.ref) (initial, []) records links
      positive
      (by
        simpa only [List.map_nil, List.append_nil]
          using reported.of_sameCancelled (next := initial) rfl)
  have cancelled := fold_projection State.cancelledGroups State.startStream
    (fun current ref => by unfold State.startStream; split <;> rfl)
    (released.newStreams.map Execution.DeliveryNode.ref) grouped.1
  exact groups.of_sameCancelled cancelled

-----------------------------------------------------------------------------------------
-- Release-time failure draining threads state and actual report output together
-----------------------------------------------------------------------------------------

/-- Each rejected task owner removed by the handler has its actual positive report.
Witness: retain the rejection, then compose the concrete failure notices in owner order.
-/
theorem State.CancelledRecordsReported.taskFailure_causes {queue : State}
    {work : Execution.Work} {events : List Execution.WorkQueueEvent} {parents}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat)
    (positive
      : ∀ task,
          queue.taskNode? occurrence = some task → ∀ group ∈ task.task.groups, 0 < errors)
    : (queue.taskFailure occurrence errors).1.CancelledRecordsReported work
        (events ++ (queue.taskFailure occurrence errors).2) := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found, List.append_nil] using reported
  | some task =>
      have loop (groups : List Execution.DeliveryNode)
          (included : groups.Subset task.task.groups) (acc : State × List Execution.WorkQueueEvent)
          (prior : acc.1.CancelledRecordsReported work (events ++ acc.2))
          (matched : acc.1.GroupNodesMatchWork work)
          (linked : acc.1.ChildLinksCanonical parents)
          : (groups.foldl (failureGroupStep errors) acc).1.CancelledRecordsReported work
              (events ++ (groups.foldl (failureGroupStep errors) acc).2) := by
        induction groups generalizing acc with
        | nil => exact prior
        | cons group rest ih =>
            apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
            obtain ⟨current, output⟩ := acc
            all_goals dsimp only [failureGroupStep]
            all_goals split
            · exact prior
            · split
              · simpa only [List.append_assoc]
                  using prior.finishGroupFailure generated matched linked canonical _
                    errors (positive task found group (included List.mem_cons_self))
              · exact prior
            · exact matched
            · split
              · exact matched.removeGroup _
              · exact matched
            · exact linked
            · split
              · exact linked.removeGroup _
              · exact linked
      rw [queue.taskFailure_eq occurrence errors task found]
      exact loop _ (List.Subset.refl _) (_, [])
        (by
          simpa only [State.CancelledRecordsReported, State.putTaskNode, List.append_nil]
            using reported)
        records links

/-- Every drain cancellation has a positive completion in its immediate or queued inventory.
Witness: successful flushes add no marker; actual child activation supplies positive
startup notices. Recursion retains that report evidence, and output permutation moves the
queued controls past later immediate output without changing any report membership.
-/
theorem State.CancelledRecordsReported.drainReadyGroups_go
    {queue : State} {work : Execution.Work} {events : List Execution.WorkQueueEvent}
    {parents : NodeRef → NodeRefs}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (positive : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors)) (fuel : Nat)
    (available : List (Occurrence × Nat) := [])
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors := by
      intro occurrence errors member; cases member)
    : (State.drainReadyGroups.go available fuel queue).1.CancelledRecordsReported work
        (events
          ++ (State.drainReadyGroups.go available fuel queue).2.1
          ++ (State.drainReadyGroups.go available fuel queue).2.2.map
              (fun failure => .groupFailure failure.group failure.errors)) := by
  have loop (fuel : Nat) (current : State) (history : List Execution.WorkQueueEvent)
      (prior : current.CancelledRecordsReported work history)
      (known : current.GroupNodesMatchWork work) (edges : current.ChildLinksCanonical parents)
      (counts : current.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
      : (State.drainReadyGroups.go available fuel current).1.CancelledRecordsReported work
          (history ++ (State.drainReadyGroups.go available fuel current).2.1
            ++ (State.drainReadyGroups.go available fuel current).2.2.map
              (fun failure => .groupFailure failure.group failure.errors)) := by
    induction fuel generalizing current history with
    | zero =>
        simpa only [State.drainReadyGroups.go, List.map_nil, List.append_nil] using prior
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · simpa only [List.map_nil, List.append_nil] using prior
        · rename_i node selected
          let closed := current.finishGroupSuccess node
          let started := closed.1.startNewWork closed.2.2 available
          let later := State.drainReadyGroups.go available fuel started.1
          have first := (prior.finishGroupSuccess node).startNewWork generated
            (known.finishGroupSuccess node) (edges.finishGroupSuccess node) canonical
            (counts.finishGroupSuccess node) closed.2.2 available licensed
          have remaining := ih started.1
            ((history ++ closed.2.1) ++ started.2.map
              (fun failure => .groupFailure failure.group failure.errors)) first
            ((known.finishGroupSuccess node).startNewWork closed.2.2 available)
            ((edges.finishGroupSuccess node).startNewWork closed.2.2 available)
            ((counts.finishGroupSuccess node).startNewWork closed.2.2 available licensed)
          apply remaining.mono
          have permutation := (List.perm_append_comm_assoc
            (started.2.map (fun failure => Execution.WorkQueueEvent.groupFailure
              failure.group failure.errors)) later.2.1
            (later.2.2.map (fun failure => Execution.WorkQueueEvent.groupFailure
              failure.group failure.errors))).append_left (history ++ closed.2.1)
          intro event member
          simp only [List.map_append, List.append_assoc] at member ⊢
          have arranged := permutation
          simp only [later, List.append_assoc] at arranged
          exact arranged.subset member
  exact loop fuel queue events reported records links positive

/-- The complete drain retains cancellation explanations through both output channels.
Witness: instantiate the bounded certificate at the actual live-node budget.
-/
theorem State.CancelledRecordsReported.drainReadyGroups
    {queue : State} {work : Execution.Work} {events : List Execution.WorkQueueEvent}
    {parents : NodeRef → NodeRefs}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work) (records : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (positive : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (available : List (Occurrence × Nat) := [])
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors := by
      intro occurrence errors member; cases member)
    : (queue.drainReadyGroups available).1.CancelledRecordsReported work
        (events
          ++ (queue.drainReadyGroups available).2.1
          ++ (queue.drainReadyGroups available).2.2.map
              (fun failure => .groupFailure failure.group failure.errors)) :=
  reported.drainReadyGroups_go generated records links canonical positive
    queue.groupNodes.length available licensed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
