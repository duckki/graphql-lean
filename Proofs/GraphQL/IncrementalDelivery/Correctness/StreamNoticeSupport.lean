import Proofs.GraphQL.IncrementalDelivery.Correctness.AnnouncedGroupProducers
import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors
import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.CompletionExistence

/-! A constructive stream-notice policy retains full healthy defer support.
This is evidence for selected finite continuations, not a public admission condition. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

/-- A stream can use one satisfied defer dependency and its full satisfied ancestry. -/
def StreamDependencySupport (ancestry : Ancestry.Assignment) (work : Work)
    (initial : NodeRefs) (matching : PublicationMatching) (events : List WorkQueueEvent)
    (failures : FailureCuts) (dependencies : NodeRefs)
    : Prop :=
  dependencies = []
  ∨ ∃ ref ∈ dependencies,
      DependencySatisfied work initial matching events failures ref
      ∧ ∀ ancestor ∈ ancestry ref,
          DependencySatisfied work initial matching events failures ancestor

/-- The stream descriptors chosen by one carrier have full support at that boundary. -/
def CarriedStreamSupport (ancestry : Ancestry.Assignment) (work : Work)
    (initial : NodeRefs) (matching : PublicationMatching) (before : List WorkQueueEvent)
    (failures : FailureCuts)
    : WorkQueueEvent → Prop
  | .groupSuccess node _ streams =>
      ∀ stream ∈ streams,
        ∃ dependencies producer,
          NodeAt work stream .stream dependencies producer
          ∧ StreamDependencySupport ancestry work initial matching
              (before ++ [.groupSuccess node [] []]) failures dependencies
  | .streamValues node values _ streams =>
      ∀ stream ∈ streams,
        ∃ dependencies producer,
          NodeAt work stream .stream dependencies producer
          ∧ StreamDependencySupport ancestry work initial matching
              (before ++ [.streamValues node values [] []]) failures dependencies
  | _ => True

/-- Each stream notice in the constructed history had full support before later cuts. -/
def StreamNoticesSupported (ancestry : Ancestry.Assignment) (work : Work)
    (initial : NodeRefs) (matching : PublicationMatching) (events : List WorkQueueEvent)
    (failures : FailureCuts)
    : Prop :=
  ∀ index event,
    events[index]? = some event
    → CarriedStreamSupport ancestry work initial matching (events.take index)
        (failures.filter (fun entry => entry.1 ≤ index)) event

/-- Notice support is unaffected by changing matching entries beyond its boundary. -/
theorem StreamDependencySupport.matching_eq
    {ancestry work initial matching next events failures dependencies}
    (support
      : StreamDependencySupport ancestry work initial matching events failures
          dependencies)
    (same : ∀ index < events.length, matching index = next index)
    : StreamDependencySupport ancestry work initial next events failures
        dependencies := by
  simpa only [StreamDependencySupport, DependencySatisfied, nodeFailed_matching_eq same,
    NodeAccounted, TaskAccounted, taskCancelled_matching_eq same,
    published_matching_eq same]
    using support

/-- Existing stream-notice evidence survives an extension preserving earlier boundaries. -/
theorem StreamNoticesSupported.append
    {ancestry work initial matching next events failures cuts event}
    (supported : StreamNoticesSupported ancestry work initial matching events failures)
    (same : ∀ index < events.length, matching index = next index)
    (past
      : ∀ index < events.length,
          cuts.filter (fun entry => entry.1 ≤ index)
          = failures.filter (fun entry => entry.1 ≤ index))
    (current
      : CarriedStreamSupport ancestry work initial next events
          (cuts.filter (fun entry => entry.1 ≤ events.length)) event)
    : StreamNoticesSupported ancestry work initial next (events ++ [event]) cuts := by
  intro index selected found
  by_cases earlier : index < events.length
  · have old : events[index]? = some selected := by
      simpa only [List.getElem?_append_left earlier] using found
    have retained := supported index selected old
    rw [List.take_append_of_le_length (Nat.le_of_lt earlier), past index earlier]
    cases selected <;> simp only [CarriedStreamSupport] at retained ⊢
    all_goals try trivial
    all_goals
      intro stream member
      obtain ⟨dependencies, producer, known, support⟩ := retained stream member
      refine ⟨dependencies, producer, known, support.matching_eq ?_⟩
      intro position before
      apply same position
      simp only [List.length_append, List.length_singleton, List.length_take] at before
      omega
  · have bounded := (List.getElem?_eq_some_iff.mp found).1
    have equal : index = events.length := by
      simp only [List.length_append, List.length_singleton] at bounded
      omega
    subst index
    have equal : selected = event := by
      simpa only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq]
        using found.symm
    subst selected
    simpa only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
      List.append_nil]
      using current

/-- Carrier support gives a dependency that remains healthy in the complete history. -/
theorem Explains.carried_stream_support_healthy
    {ancestry bound roles work groups streams events matching failures index event plain
      node dependencies producer}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (selected : events[index]? = some event)
    (sameValue : IsValue plain ↔ IsValue event)
    (sameCompleted : eventCompleted plain = eventCompleted event)
    (known : NodeAt work node .stream dependencies producer)
    (support
      : StreamDependencySupport ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching (events.take index ++ [plain])
          (failures.filter (fun entry => entry.1 ≤ index)) dependencies)
    : dependencies = []
      ∨ ∃ ref ∈ dependencies, ¬NodeFailed work matching events failures ref := by
  rcases support with empty | ⟨ref, member, supported, ancestors⟩
  · exact Or.inl empty
  refine Or.inr ⟨ref, member, ?_⟩
  have shorter := explained.after_carrier_before_settlements selected
  have actual : events.take (index + 1) = events.take index ++ [event] := by
    rw [List.take_add_one, selected, Option.toList_some]
  have sameFailure := causality_carrier_eq (work := work) (matching := matching)
    (events := events.take index)
    (failures := failures.filter (fun entry => entry.1 ≤ index)) sameValue
  have samePublication : Published matching (events.take index ++ [plain])
      = Published matching (events.take index ++ [event]) := by
    funext occurrence
    apply propext
    simp only [published_append_singleton_iff, sameValue]
  have sameClosure : completedRefs (events.take index ++ [plain])
      = completedRefs (events.take index ++ [event]) := by
    simp only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      sameCompleted]
  have accounting (ref) (satisfied : DependencySatisfied work
      ((groups ++ streams).map DeliveryNode.ref) matching (events.take index ++ [plain])
      (failures.filter (fun entry => entry.1 ≤ index)) ref)
      : ¬NodeFailed work matching (events.take (index + 1))
          (failures.filter (fun entry => entry.1 ≤ index)) ref
        ∧ NodeAccounted work matching (events.take (index + 1))
            (failures.filter (fun entry => entry.1 ≤ index)) ref := by
    have healthy : ¬NodeFailed work matching (events.take (index + 1))
        (failures.filter (fun entry => entry.1 ≤ index)) ref := by
      rw [actual, ← sameFailure.1]
      exact satisfied.1
    refine ⟨healthy, ?_⟩
    rcases satisfied.2 with absent | closed | ⟨_, accounted⟩
    · intro occurrence owners ⟨birth, payload, task⟩ contributes
      obtain ⟨owner, kind, parents, source, descriptor, same⟩ := task.owner_known contributes
      exact False.elim (absent ⟨source, owner, kind, parents, descriptor, same⟩)
    · rw [sameClosure, ← actual] at closed
      exact (shorter.completed_accounted closed).resolve_left healthy
    · simpa only [actual, NodeAccounted, TaskAccounted, sameFailure.2, samePublication]
        using accounted
  obtain ⟨group, parents, birth, descriptor, same⟩ := stream_dependency_group known member
  apply Explains.supported_defer_dependency_stays_healthy_before_next_settlements
    valid coherent roleCoherent explained shorter (Nat.le_refl _)
    (same ▸ node_ref_role roleCoherent descriptor) (accounting ref supported)
  exact fun ancestor member => accounting ancestor (ancestors ancestor member)

/-- A producer-free stream has no enclosing deferred owners. -/
theorem initial_stream_dependencies_empty {work node dependencies producer}
    (known : NodeAt work node .stream dependencies producer)
    (eligible
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .stream
          dependencies producer)
    : dependencies = [] := by
  have root : producer = none := by
    cases producer with
    | none => rfl
    | some occurrence =>
        have impossible := eligible.2.2.1 occurrence rfl
        simp [Published] at impossible
  subst producer
  obtain ⟨address, items, located⟩ := known
  exact located_producer_context located

/-- Supported stream notices retain at least one healthy dependency whenever any exist. -/
theorem StreamNoticesSupported.announced_stream_dependency
    {ancestry bound roles work groups streams events matching failures node dependencies
      producer}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (allocated : (streamAllocationRefs work).Nodup)
    (explained : Explains work groups streams events matching failures)
    (supported
      : StreamNoticesSupported ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (known : NodeAt work node .stream dependencies producer)
    (announced
      : node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    : dependencies = []
      ∨ ∃ ref ∈ dependencies, ¬NodeFailed work matching events failures ref := by
  rcases List.mem_append.mp announced with initial | carried
  · obtain ⟨notice, member, same⟩ := List.mem_map.mp initial
    rcases List.mem_append.mp member with group | stream
    · obtain ⟨parents, birth, descriptor, _⟩ := explained.1.1.2.1 notice group
      exact False.elim (stream_group_refs_distinct roleCoherent known descriptor same.symm)
    · obtain ⟨parents, birth, descriptor, eligible⟩ := explained.1.1.2.2 notice stream
      have equal := (streamMetadata_unique allocated known descriptor same.symm).1
      exact Or.inl (equal.trans (initial_stream_dependencies_empty descriptor eligible))
  · obtain ⟨event, member, notice⟩ := List.mem_flatMap.mp carried
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    have atBoundary := supported index event selected
    have allowed := explained.eventAllowed index event selected
    simp only [EventAllowed,
      List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)] at allowed
    have carrier {plain newGroups newStreams}
        (sameValue : IsValue plain ↔ IsValue event)
        (sameCompleted : eventCompleted plain = eventCompleted event)
        (notices : Announcements work ((groups ++ streams).map DeliveryNode.ref) matching
          (events.take index ++ [plain]) (failures.filter (fun entry => entry.1 ≤ index))
          newGroups newStreams)
        (present : node.ref ∈ (newGroups ++ newStreams).map DeliveryNode.ref)
        (support : ∀ stream ∈ newStreams, ∃ parents birth,
          NodeAt work stream .stream parents birth
          ∧ StreamDependencySupport ancestry work ((groups ++ streams).map DeliveryNode.ref)
              matching (events.take index ++ [plain])
              (failures.filter (fun entry => entry.1 ≤ index)) parents)
        : dependencies = [] ∨ ∃ ref ∈ dependencies,
            ¬NodeFailed work matching events failures ref := by
      obtain ⟨notice, member, same⟩ := List.mem_map.mp present
      rcases List.mem_append.mp member with group | stream
      · obtain ⟨parents, birth, descriptor, _⟩ := notices.2.1 notice group
        exact False.elim (stream_group_refs_distinct roleCoherent known descriptor same.symm)
      · obtain ⟨parents, birth, descriptor, full⟩ := support notice stream
        have equal := (streamMetadata_unique allocated known descriptor same.symm).1
        rw [equal]
        exact Explains.carried_stream_support_healthy valid coherent roleCoherent explained
          selected sameValue sameCompleted descriptor full
    cases event <;> simp only [eventPending, List.not_mem_nil] at notice
    all_goals try contradiction
    case groupSuccess carrierNode newGroups newStreams =>
      exact carrier (plain := .groupSuccess carrierNode [] []) Iff.rfl rfl
        allowed.2.2.2.2 notice atBoundary
    case streamValues carrierNode values newGroups newStreams =>
      obtain ⟨owners, birth, value, _, _, _, _, notices⟩ := allowed
      exact carrier (plain := .streamValues carrierNode values [] []) Iff.rfl rfl
        notices notice atBoundary

/-- Positive direct causes suffice to close all failed IDs in a supported construction.
Announced groups exclude inherited failure; supported streams retain a healthy defer
dependency. Actual notice provenance excludes unavailable producers. -/
theorem Explains.openFailureCauses_of_supported_streams
    {ancestry bound roles work groups streams events matching failures}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (allocated : (streamAllocationRefs work).Nodup)
    (positive : ExecutionErrors.WorkPositive work)
    (explained : Explains work groups streams events matching failures)
    (supported
      : StreamNoticesSupported ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    : OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref)
        matching events failures := by
  intro ref opened failed
  obtain ⟨node, kind, parents, birth, descriptor, same, available⟩ :=
    Explains.announced_producer_available explained opened.1
  have recorded : HasRecordedFailure work failures events.length ref := by
    cases kind with
    | group =>
        apply Classical.byContradiction
        intro noRecord
        exact Explains.announced_group_healthy_of_no_recorded_failure valid coherent
          roleCoherent explained descriptor (same ▸ opened.1) (same ▸ noRecord) (same ▸ failed)
    | stream =>
        have snapshot := explained.nodeFailed_snapshot failed
        cases snapshot with
        | task known contributes recorded => exact ⟨_, _, recorded, known, contributes⟩
        | groupDependency known _ _ =>
            obtain ⟨group, producer, known, equal⟩ := known
            exact False.elim (stream_group_refs_distinct roleCoherent descriptor known
              (same.trans equal.symm))
        | streamDependencies known nonempty failures =>
            obtain ⟨stream, producer, known, equal⟩ := known
            have announced := equal ▸ opened.1
            rcases supported.announced_stream_dependency valid coherent roleCoherent allocated
                explained known announced with empty | ⟨dependency, member, healthy⟩
            · exact False.elim (nonempty empty)
            · exact False.elim (healthy (explained.snapshot_nodeFailed
                (failures dependency member)))
        | producers _ noRoot unpublished _ =>
            cases birth with
            | none => exact False.elim (noRoot ⟨node, .stream, parents, descriptor, same⟩)
            | some source =>
                exact False.elim (unpublished source
                  ⟨node, .stream, parents, descriptor, same⟩ (available source rfl))
  obtain ⟨occurrence, owners, settled, ⟨producer, payload, task⟩, contributes⟩ := recorded
  obtain ⟨entry, member, occurrenceEq⟩ := List.mem_map.mp settled
  have inCuts := (List.mem_filter.mp member).1
  have fails := explained.2.1.recorded_payload_fails
    (by simpa only [← occurrenceEq] using inCuts) task
  exact ⟨payload.failure.getD 0,
    .of_task task settled contributes fails (positive.task task fails)⟩

/-- Causal failure always identifies represented node metadata, independently of admission. -/
theorem nodeFailed_hasProducer {work matching events failures ref}
    (failure : NodeFailed work matching events failures ref)
    : ∃ producer, NodeHasProducer work ref producer := by
  obtain ⟨cut, _, _, snapshot⟩ := failure
  cases snapshot with
  | task known member _ =>
      obtain ⟨producer, payload, task⟩ := known
      obtain ⟨node, kind, dependencies, birth, descriptor, same⟩ := task.owner_known member
      exact ⟨birth, node, kind, dependencies, descriptor, same⟩
  | groupDependency known _ _ =>
      obtain ⟨node, producer, descriptor, same⟩ := known
      exact ⟨producer, node, .group, _, descriptor, same⟩
  | streamDependencies known _ _ =>
      obtain ⟨node, producer, descriptor, same⟩ := known
      exact ⟨producer, node, .stream, _, descriptor, same⟩
  | producers known _ _ _ => exact known

/-- If every group is initially announced, every admitted stream notice has full support.
Initial group ancestry names only absent work refs, so stream release cannot hide a
still-open represented ancestor. This specialization does not require a future policy. -/
theorem Explains.streamNoticesSupported_of_initial_groups
    {ancestry bound roles work groups streams events matching failures}
    (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (initialGroups
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer
          → node.ref ∈ groups.map DeliveryNode.ref)
    : StreamNoticesSupported ancestry work ((groups ++ streams).map DeliveryNode.ref)
        matching events failures := by
  have support {initial matching events failures node dependencies producer}
      (known : NodeAt work node .stream dependencies producer)
      (eligible : CanAnnounce work initial matching events failures node .stream
        dependencies producer)
      : StreamDependencySupport ancestry work initial matching events failures dependencies := by
    rcases eligible.2.2.2 with empty | ⟨ref, member, satisfied⟩
    · exact Or.inl empty
    refine Or.inr ⟨ref, member, satisfied, ?_⟩
    obtain ⟨group, parents, birth, descriptor, same⟩ := stream_dependency_group known member
    obtain ⟨notice, inGroups, equal⟩ := List.mem_map.mp (initialGroups _ _ _ descriptor)
    obtain ⟨ancestors, source, noticed, _⟩ := explained.1.1.2.1 notice inGroups
    have absent := Initializes.initial_group_dependencies_absent coherent roleCoherent
      explained.1 noticed inGroups
    intro ancestor selected
    have noProducer : ¬∃ source, NodeHasProducer work ancestor source := by
      apply absent ancestor
      simpa only [DeferOnly.node_dependencies coherent noticed, equal, same] using selected
    exact ⟨fun failure => noProducer (nodeFailed_hasProducer failure), Or.inl noProducer⟩
  intro index event selected
  have allowed := explained.eventAllowed index event selected
  simp only [EventAllowed,
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)] at allowed
  cases event <;> simp only [CarriedStreamSupport]
  all_goals try trivial
  case groupSuccess node newGroups newStreams =>
    intro stream member
    obtain ⟨dependencies, producer, known, eligible⟩ := allowed.2.2.2.2.2.2 stream member
    exact ⟨dependencies, producer, known, support known eligible⟩
  case streamValues node values newGroups newStreams =>
    obtain ⟨owners, birth, value, _, _, _, _, notices⟩ := allowed
    intro stream member
    obtain ⟨dependencies, producer, known, eligible⟩ := notices.2.2 stream member
    exact ⟨dependencies, producer, known, support known eligible⟩

end GraphQL.IncrementalDelivery.Correctness
