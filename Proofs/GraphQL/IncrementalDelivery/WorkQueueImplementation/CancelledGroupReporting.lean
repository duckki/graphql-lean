import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrainOutput
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrors

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
group or one of its full registration ancestors. `events` is accumulated output and
`work` supplies record provenance, including taskless ancestor records.
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
    · rename_i blocked
      intro node dependencies known member
      rcases List.mem_append.mp member with old | added
      · exact reported node dependencies known old
      · have same : node.ref = group.node.ref := List.mem_singleton.mp added
        obtain ⟨groupDependencies, groupKnown, parentEq⟩ := matching
        obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
        have equalDependencies : dependencies = groupDependencies := by
          rw [canonical _ _ known, canonical _ _ groupKnown, same]
        cases atParent : group.parent with
        | none => simp [atParent] at blocked
        | some parent =>
            have cancelled : parent ∈ queue.cancelledGroups := by
              simpa [atParent] using blocked
            have head : dependencies.head? = some parent :=
              equalDependencies.symm ▸ (parentEq.symm.trans atParent)
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

/-- A complete registration batch preserves report provenance in any candidate order.
Witness: thread refused-child inheritance through registration; parent linking leaves the
cancellation registry unchanged. No notice is emitted for a refused child.
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
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  have fold (more : List Group) (current : State)
      (prior : current.CancelledRecordsReported work events) (subset : more.Subset groups)
      : (more.foldl State.addGroup current).CancelledRecordsReported work events := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        exact ih _ (prior.addGroup generated group (matching group (subset List.mem_cons_self)))
          (fun _ member => subset (List.mem_cons_of_mem _ member))
  have registered := fold fresh queue reported
    (fun _ member => (List.mem_filter.mp member).1)
  intro node dependencies known member
  rw [State.addGroups_cancelledGroups] at member
  exact registered node dependencies known member

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

/-- Activation preserves cancellation report origins exactly.
Witness: starting released tasks and streams changes no cancellation marker.
-/
theorem State.CancelledRecordsReported.startNewWork {queue : State} {work events}
    (reported : queue.CancelledRecordsReported work events) (released : NewWork)
    : (queue.startNewWork released).CancelledRecordsReported work events := by
  intro node dependencies known member
  rw [State.startNewWork_cancelledGroups] at member
  exact reported node dependencies known member

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
        (events ++ [(queue.finishGroupFailure group errors).2]) := by
  exact (reported.append [.groupFailure group.group.node errors]).removeGroup
    generated records links canonical positive (by simp)

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

/-- Every drain closure preserves cancellation markers' actual positive report origins.
Witness: the output-aware budget induction threads report evidence, canonical live links,
record provenance, and positive caches. Retained cached failures supply their actual
error counts; successful release adds no markers. This does not assume source admission.
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
    (positive : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors)) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.CancelledRecordsReported work
        (events ++ (State.drainReadyGroups.go fuel queue).2) := by
  let invariant (current : State) (history : List Execution.WorkQueueEvent) :=
    current.CancelledRecordsReported work history
    ∧ current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents
    ∧ current.CachedErrorsSatisfy (fun _ errors => 0 < errors)
  have output := State.drainReadyGroups_go_outputPreserves invariant
    (fun current history node prior _ _ _ _ =>
      ⟨(prior.1.finishGroupSuccess node).startNewWork _,
        (prior.2.1.finishGroupSuccess node).startNewWork _,
        (prior.2.2.1.finishGroupSuccess node).startNewWork _,
        (prior.2.2.2.finishGroupSuccess node).startNewWork _⟩)
    (fun current history node occurrence errors prior _ _ selected => by
      obtain ⟨_, task, found, rejected⟩ := State.rejectedTask?_sound selected
      have positive : ∀ other, current.taskNode? occurrence = some other →
          ∀ group ∈ other.task.groups, 0 < errors := by
        intro other lookup group member
        have same := Option.some.inj (lookup.symm.trans found)
        subst other
        exact prior.2.2.2 task (List.mem_of_find?_eq_some found) errors rejected group member
      exact ⟨prior.1.taskFailure_causes generated prior.2.1 prior.2.2.1 canonical
          occurrence errors positive,
        prior.2.1.taskFailure occurrence errors,
        prior.2.2.1.taskFailure occurrence errors,
        prior.2.2.2.taskFailure occurrence errors positive⟩)
    (show invariant queue events from ⟨reported, records, links, positive⟩) fuel
  exact output.1

/-- The complete release drain retains the same report-origin invariant.
Witness: instantiate output-aware draining at the implementation's live-node budget.
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
    (positive : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors))
    : queue.drainReadyGroups.1.CancelledRecordsReported work
        (events ++ queue.drainReadyGroups.2) :=
  reported.drainReadyGroups_go generated records links canonical positive
    queue.groupNodes.length

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
