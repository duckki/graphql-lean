import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferredPhase
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata

/-! Finish initially covered root deferred tasks and their nested stream descendants.
The construction reserves a final healthy group carrier, or uses justified cancellation.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Deferred-phase publications and control-only suffixes
-----------------------------------------------------------------------------------------

/-- Every publication in a deferred phase matches an execution-group occurrence, not a
stream item. Witness: the only permitted value event is an object publication, whose
provenance is a deferred task even if its payload value happens to equal a stream item's
value.
-/
theorem deferredPhase_published_deferred
    {work groups streams events matching failures occurrence}
    (explained : Explains work groups streams events matching failures)
    (phase : ∀ event ∈ events, DeferredPhaseEvent event)
    (published : Published matching events occurrence)
    : ∃ address, occurrence = .executionGroup address := by
  obtain ⟨index, event, selected, value, same⟩ := published
  have allowed := explained.2.2 index event selected
  have permitted := phase event (List.mem_of_getElem? selected)
  cases event <;> simp only [DeferredPhaseEvent, IsValue] at permitted value
  all_goals try contradiction
  rename_i owner values
  obtain ⟨owners, producer, ⟨path, data, errors, deliveryGroups⟩, _, known, _, _⟩ := allowed
  have task : TaskAt work occurrence owners producer (.object path (.ok (data, errors))) := by
    simpa only [List.length_take,
      Nat.min_eq_left
        (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1), same]
      using known
  cases StructuralEquivalence.taskAt_of_current task with
  | executionGroup => exact ⟨_, rfl⟩

/-- A finite list of control events preserves stream coverage under unchanged failures.
Witness: apply the single-control preservation theorem successively; controls publish no
new producer, irrespective of their pending notices or completion entries.
-/
theorem streamsNotified_append_controls {work initial matching events failed}
    (notified : StreamsNotified work initial matching events failed)
    {tail : List WorkQueueEvent} (controls : ∀ event ∈ tail, ¬IsValue event)
    : StreamsNotified work initial matching (events ++ tail) failed := by
  induction tail generalizing events with
  | nil => simpa using notified
  | cons event tail ih =>
      have next := notified.append_control (controls event (by simp)) (List.Subset.refl failed)
      simpa only [List.append_assoc, List.singleton_append]
        using ih next (fun other member => controls other (by simp [member]))

-----------------------------------------------------------------------------------------
-- Complete initially covered root deferred work and all remaining streams
-----------------------------------------------------------------------------------------

/-- Root deferred tasks with initially covered owners admit a complete run, including
arbitrary shared ownership and nested streams. Root streams must also be initially
covered. Witness: finish the deferred phase, close the accounted groups while reserving
one healthy success carrier, then apply stream continuation. If no group is healthy,
dependent streams are failed and already covered root streams suffice. No terminal
history, success premise, or extra scheduler law is assumed.
-/
theorem completeRun_exists_of_initial_deferred_coverage
    {paths bound roles work groups streams}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (initialized : Initializes work groups streams)
    (roots
      : ∀ address owners producer payload,
          TaskAt work (.executionGroup address) owners producer payload → producer = none)
    (covered
      : ∀ address owners producer payload,
          TaskAt work (.executionGroup address) owners producer payload
          → owners ≠ [] ∧ ∀ ref ∈ owners, ref ∈ (groups ++ streams).map DeliveryNode.ref)
    (rootStreams
      : ∀ node dependencies,
          NodeAt work node .stream dependencies none
          → node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
    : ∃ history, AdmissibleRun work history := by
  classical
  have groupInitial {node dependencies producer}
      (known : NodeAt work node .group dependencies producer)
      : node.ref ∈ groups.map DeliveryNode.ref := by
    have announced : node.ref ∈ (groups ++ streams).map DeliveryNode.ref := by
      cases StructuralEquivalence.nodeAt_of_current known with
      | group located member =>
          have task := TaskAt.executionGroup located.toCurrent
          exact (covered _ _ _ _ task).2 _ (List.mem_map.mpr ⟨_, member, rfl⟩)
    rw [List.map_append] at announced
    rcases List.mem_append.mp announced with inGroups | inStreams
    · exact inGroups
    · obtain ⟨stream, member, same⟩ := List.mem_map.mp inStreams
      obtain ⟨dependencies, producer, streamKnown, _⟩ :=
        initialized.1.2.2 stream member
      exact False.elim (stream_group_refs_distinct roleCoherent streamKnown known same)
  have dependenciesCovered {node dependencies producer}
      (known : NodeAt work node .stream dependencies producer)
      : ∀ ref ∈ dependencies, ref ∈ groups.map DeliveryNode.ref := by
    obtain ⟨address, items, located⟩ := known
    have context := located_producer_context located
    cases producer with
    | none => simp only [context, List.not_mem_nil, false_implies, implies_true]
    | some occurrence =>
        cases occurrence with
        | item => simp only [context, List.not_mem_nil, false_implies, implies_true]
        | executionGroup producerAddress =>
            obtain ⟨ancestor, path, result, task⟩ := context
            obtain ⟨fragments, taskPath, outcome, children, enclosing, taskLocated, rfl, _⟩ := task
            intro ref member
            obtain ⟨fragment, inFragments, rfl⟩ := List.mem_map.mp member
            exact groupInitial (.group taskLocated inFragments)
  obtain ⟨events, matching, failures, explained, phase, deferred, remainsOpen⟩ :=
    finish_root_deferred_tasks coherent initialized roots covered
  have groupAccounted {node dependencies producer}
      (known : NodeAt work node .group dependencies producer)
      : NodeAccounted work matching events failures node.ref := by
    rintro occurrence owners ⟨producer, payload, task⟩ contributes
    cases StructuralEquivalence.taskAt_of_current task with
    | executionGroup located => exact deferred _ _ _ _ task
    | item located entry =>
        exact False.elim (stream_group_refs_distinct roleCoherent
          (NodeAt.stream located.toCurrent) known (List.mem_singleton.mp contributes).symm)
  have accounted (ref : NodeRef) (member : ref ∈ groups.map DeliveryNode.ref)
      : NodeAccounted work matching events failures ref := by
    obtain ⟨node, inGroups, rfl⟩ := List.mem_map.mp member
    obtain ⟨dependencies, producer, known, _⟩ := initialized.1.2.1 node inGroups
    exact groupAccounted known
  have announced (ref : NodeRef) (member : ref ∈ groups.map DeliveryNode.ref)
      : ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events := by
    apply List.mem_append_left
    simpa only [List.map_append]
      using List.mem_append_left (streams.map DeliveryNode.ref) member
  by_cases available : ∃ node ∈ groups, ¬NodeFailed work matching events failures node.ref
  · obtain ⟨anchor, inGroups, healthy⟩ := available
    obtain ⟨dependencies, producer, known, _⟩ :=
      initialized.1.2.1 anchor inGroups
    have anchorMember : anchor.ref ∈ groups.map DeliveryNode.ref :=
      List.mem_map.mpr ⟨anchor, inGroups, rfl⟩
    have anchorOpen :=
      remainsOpen anchor.ref
        (by
          simpa only [List.map_append]
            using List.mem_append_left (streams.map DeliveryNode.ref) anchorMember)
        healthy
    let others := (groups.map DeliveryNode.ref).filter (fun ref => ref != anchor.ref)
    obtain ⟨closures, _, _, closedOthers, completedOthers, selected⟩ :=
      explained.close_accounted_refs others
        (fun ref member => announced ref (List.mem_filter.mp member).1)
        (fun ref member => accounted ref (List.mem_filter.mp member).1)
    have reserved := anchorOpen.append_unselected selected (by simp [others])
    have dependenciesClosed {newGroups newStreams : List DeliveryNode}
        : StreamDependenciesCompleted work
            (events ++ closures ++ [.groupSuccess anchor newGroups newStreams]) := by
      intro node dependencies producer descriptor ref member
      have inRefs := dependenciesCovered descriptor ref member
      by_cases same : ref = anchor.ref
      · simp [completedRefs, eventCompleted, same]
      · have previous := completedOthers ref (List.mem_filter.mpr ⟨inRefs, by simpa using same⟩)
        simpa only [completedRefs, List.flatMap_append]
          using List.mem_append_left
            (completedRefs [.groupSuccess anchor newGroups newStreams]) previous
    obtain ⟨newGroups, newStreams, released, notified⟩ :=
      closedOthers.complete_group_streams_notified known reserved
        (by
          rw [(causality_append_eq
            (fun _ member => explained.2.1.cut_le member) closures).1]
          exact healthy)
        ((accounted anchor.ref anchorMember).append closures)
        dependenciesClosed
    have preserved := (deferred.extend (List.Subset.refl _) closures).extend
      (List.Subset.refl _) [.groupSuccess anchor newGroups newStreams]
    obtain ⟨tail, run⟩ := released_streams_run_extension coherent released preserved
      dependenciesClosed notified (WorkBatching.singletons _)
    exact ⟨_, run⟩
  · have allFailed (ref : NodeRef) (member : ref ∈ groups.map DeliveryNode.ref)
        : NodeFailed work matching events failures ref := by
      obtain ⟨node, inGroups, rfl⟩ := List.mem_map.mp member
      exact Classical.byContradiction (fun healthy => available ⟨node, inGroups, healthy⟩)
    have notified : StreamsNotified work ((groups ++ streams).map DeliveryNode.ref)
        matching events failures := by
      intro node dependencies producer descriptor produced healthy
      cases producer with
      | none => exact List.mem_append_left _ (rootStreams node dependencies descriptor)
      | some occurrence =>
          obtain ⟨address, rfl⟩ := deferredPhase_published_deferred explained phase
            (produced occurrence rfl)
          obtain ⟨route, items, located⟩ := descriptor
          obtain ⟨ancestor, path, result, task⟩ := located_producer_context located
          exact False.elim (healthy (explained.snapshot_nodeFailed
            (.streamDependencies ⟨_, _, NodeAt.stream located, rfl⟩
              (covered _ _ _ _ task).1
              (fun ref member => explained.nodeFailed_snapshot
                (allFailed ref (dependenciesCovered (NodeAt.stream located) ref member))))))
    obtain ⟨closures, _, controls, closed, completed, _⟩ :=
      explained.close_accounted_refs (groups.map DeliveryNode.ref) announced accounted
    have dependenciesClosed : StreamDependenciesCompleted work (events ++ closures) :=
      fun _ _ _ descriptor ref member => completed ref (dependenciesCovered descriptor ref member)
    have preserved := deferred.extend (List.Subset.refl _) closures
    have retained := streamsNotified_append_controls notified
      (fun event member => (controls event member).2)
    obtain ⟨tail, run⟩ := released_streams_run_extension coherent closed preserved
      dependenciesClosed retained (WorkBatching.singletons _)
    exact ⟨_, run⟩

/-- Covering only the deferred owners in a valid initial frontier already suffices for
root-deferred complete-run existence. Witness: enlarge the frontier to all eligible refs;
root streams have no producer or enclosing dependencies, so the enlarged frontier covers
them.
The execution queue constructor remains opaque, and no completion ordering is prescribed.
-/
theorem completeRun_exists_of_root_deferred_coverage
    {paths bound roles work groups streams}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (initialized : Initializes work groups streams)
    (roots
      : ∀ address owners producer payload,
          TaskAt work (.executionGroup address) owners producer payload → producer = none)
    (covered
      : ∀ address owners producer payload,
          TaskAt work (.executionGroup address) owners producer payload
          → owners ≠ [] ∧ ∀ ref ∈ owners, ref ∈ (groups ++ streams).map DeliveryNode.ref)
    : ∃ history, AdmissibleRun work history := by
  obtain ⟨newGroups, newStreams, enlarged, covers⟩ := initialized.covering_exists
  have retained {ref} (member : ref ∈ (groups ++ streams).map DeliveryNode.ref)
      : ref ∈ (newGroups ++ newStreams).map DeliveryNode.ref := by
    obtain ⟨node, inInitial, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp inInitial with group | stream
    · obtain ⟨dependencies, producer, known, eligible⟩ :=
        initialized.1.2.1 node group
      exact covers node .group dependencies producer known eligible
    · obtain ⟨dependencies, producer, known, eligible⟩ :=
        initialized.1.2.2 node stream
      exact covers node .stream dependencies producer known eligible
  apply completeRun_exists_of_initial_deferred_coverage coherent roleCoherent enlarged
    roots
  · intro address owners producer payload known
    obtain ⟨nonempty, announced⟩ := covered address owners producer payload known
    exact ⟨nonempty, fun ref member => retained (announced ref member)⟩
  · intro node dependencies known
    have empty : dependencies = [] := by
      obtain ⟨address, items, located⟩ := known
      exact located_producer_context located
    apply covers node .stream dependencies none known
    exact ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨fun failure => failure.nonempty rfl, Or.inl rfl⟩, by simp, Or.inl empty⟩

end GraphQL.IncrementalDelivery.Correctness
