import Proofs.GraphQL.IncrementalDelivery.Correctness.NestedStreamExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.HealthyGroupStreamProgress
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles

/-! A deferred producer can release arbitrarily nested stream-only child work.
Both producer outcomes admit complete runs; no output history is supplied as a premise.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Structural facts for one deferred producer and its stream descendants
-----------------------------------------------------------------------------------------

/-- Below a single deferred producer, locations are stream-only, have a producer, and
retain either its shared defer refs or no enclosing refs. Witness: structural navigation;
stream-item edges reset the enclosing defer context.
-/
theorem deferredStreams_located
    {fragments path result children address current producer owners}
    (onlyStreams : StreamOnly children)
    (located
      : Located (.executionGroup fragments path result children) address current producer
          owners)
    : (address = []
        ∧ current = .executionGroup fragments path result children
        ∧ producer = none
        ∧ owners = [])
      ∨ (StreamOnly current
          ∧ producer ≠ none
          ∧ (owners = [] ∨ owners = fragments.map (fun group => group.node.ref))) := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | left _ ih =>
      rcases ih with ⟨_, impossible, _, _⟩ | ⟨only, birth, owners⟩
      · cases impossible
      · rw [StreamOnly] at only
        exact Or.inr ⟨only.1.withoutDeclarations, birth, owners⟩
  | right _ ih =>
      rcases ih with ⟨_, impossible, _, _⟩ | ⟨only, birth, owners⟩
      · cases impossible
      · rw [StreamOnly] at only
        exact Or.inr ⟨only.2.withoutDeclarations, birth, owners⟩
  | executionGroup _ ih =>
      rcases ih with ⟨rfl, same, rfl, rfl⟩ | ⟨impossible, _, _⟩
      · cases same
        exact Or.inr ⟨onlyStreams.withoutDeclarations, by simp, Or.inr rfl⟩
      · simp only [StreamOnly] at impossible
  | item _ entry ih =>
      rcases ih with ⟨_, impossible, _, _⟩ | ⟨only, _, _⟩
      · cases impossible
      · rw [StreamOnly] at only
        exact Or.inr ⟨(only _ (List.mem_of_getElem? entry)).withoutDeclarations, by simp, Or.inl rfl⟩

/-- The wrapper's sole deferred task is its root task. Witness: every deeper location
is stream-only, so cannot contain another execution-group boundary.
-/
theorem deferredStreams_deferred_task
    {fragments path result children address owners producer payload}
    (onlyStreams : StreamOnly children)
    (known
      : TaskAt (.executionGroup fragments path result children) (.executionGroup address)
          owners producer payload)
    : address = []
      ∧ owners = fragments.map (fun group => group.node.ref)
      ∧ producer = none
      ∧ payload = .object path result.deliveryResult := by
  obtain ⟨groups, taskPath, outcome, childWork, enclosing, located, rfl, rfl⟩ := known
  rcases deferredStreams_located onlyStreams located with
    ⟨rfl, same, rfl, rfl⟩ | ⟨impossible, _, _⟩
  · cases same
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [StreamOnly] at impossible

/-- No stream item below the deferred wrapper is producer-free. Witness: the stream
location is below the root and therefore has a structural producer.
-/
theorem deferredStreams_root_task
    {fragments path result children occurrence owners payload}
    (onlyStreams : StreamOnly children)
    (known
      : TaskAt (.executionGroup fragments path result children) occurrence owners none
          payload)
    : occurrence = .executionGroup [] := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      exact congrArg Occurrence.executionGroup (deferredStreams_deferred_task onlyStreams known).1
  | item located entry =>
      rcases deferredStreams_located onlyStreams located.toCurrent with
        ⟨_, impossible, _, _⟩ | ⟨_, impossible, _⟩
      · cases impossible
      · exact False.elim (impossible rfl)

/-- Every stream below the wrapper has either no defer dependencies or the producer's
owners.
Witness: its location's enclosing-owner context.
-/
theorem deferredStreams_stream_dependencies
    {fragments path result children stream dependencies producer}
    (onlyStreams : StreamOnly children)
    (known
      : NodeAt (.executionGroup fragments path result children) stream .stream
          dependencies producer)
    : dependencies = [] ∨ dependencies = fragments.map (fun group => group.node.ref) := by
  obtain ⟨address, items, located⟩ := known
  rcases deferredStreams_located onlyStreams located with
    ⟨_, impossible, _, _⟩ | ⟨_, _, owners⟩
  · cases impossible
  · exact owners

/-- Every group descriptor is one of the dependency-free root producer's owners.
Witness: below the root every location is stream-only, and each root fragment has no
parents. Stream descendants cannot introduce additional group descriptors.
-/
theorem sharedDeferredStreams_group
    {nodes : List DeliveryNode} {path result children node dependencies producer}
    (onlyStreams : StreamOnly children)
    (known
      : NodeAt (.executionGroup (nodes.map (fun node => { node })) path result children)
          node .group dependencies producer)
    : dependencies = [] ∧ producer = none ∧ node ∈ nodes := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      rcases deferredStreams_located onlyStreams located.toCurrent with
        ⟨rfl, same, rfl, rfl⟩ | ⟨impossible, _, _⟩
      · cases same
        obtain ⟨node, included, same⟩ := List.mem_map.mp member
        cases same
        exact ⟨rfl, rfl, included⟩
      · simp only [StreamOnly] at impossible

/-- A successful root deferred producer keeps all its groups healthy in every explained
history, even when nested stream items fail. Witness: the sole group task has a fixed
successful payload; other tasks have stream refs of a different role. Root groups have
neither failing defer dependencies nor structural producers.
-/
theorem sharedDeferredStreams_success_groups_healthy
    {nodes : List DeliveryNode}
    {roles path result data errors children groups streams events matching failures}
    (onlyStreams : StreamOnly children)
    (roleCoherent
      : RefRoles.WorkRoles roles
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    (explained
      : Explains (.executionGroup (nodes.map (fun node => { node })) path result children)
          groups streams events matching failures)
    (success : result.deliveryResult = .ok (data, errors))
    {node dependencies birth}
    (known
      : NodeAt (.executionGroup (nodes.map (fun node => { node })) path result children)
          node .group dependencies birth)
    : ¬NodeFailed
        (.executionGroup (nodes.map (fun node => { node })) path result children) matching
        events failures node.ref := by
  rintro ⟨cut, _, _, cause⟩
  cases cause with
  | task projected owner recorded =>
      obtain ⟨producer, payload, task⟩ := projected
      cases StructuralEquivalence.taskAt_of_current task with
      | executionGroup located =>
          have same := (deferredStreams_deferred_task onlyStreams task).2.2.2
          obtain ⟨entry, member, equal⟩ := List.mem_map.mp recorded
          have member := (List.mem_filter.mp member).1
          have fails := explained.2.1.recorded_payload_fails
            (by simpa only [← equal] using member) task
          simp only [same, success, Payload.failure, Option.isSome_none,
            Bool.false_eq_true] at fails
      | item located entry =>
          exact stream_group_refs_distinct roleCoherent (NodeAt.stream located.toCurrent)
            known (List.mem_singleton.mp owner).symm
  | groupDependency projected member _ =>
      obtain ⟨group, producer, descriptor, _⟩ := projected
      rw [(sharedDeferredStreams_group onlyStreams descriptor).1] at member
      cases member
  | streamDependencies projected _ _ =>
      obtain ⟨stream, producer, descriptor, same⟩ := projected
      exact stream_group_refs_distinct roleCoherent descriptor known same
  | producers _ noRoot _ _ =>
      have root := (sharedDeferredStreams_group onlyStreams known).2.1
      subst birth
      exact noRoot ⟨node, .group, dependencies, known, rfl⟩

-----------------------------------------------------------------------------------------
-- Construct the deferred publication/closure or the justified failure
-----------------------------------------------------------------------------------------

/-- A shared deferred producer with dependency-free owners and stream-only children admits a
complete run for local attachments and positive producer/item failures. Witness: announce
the owner refs, publish
once, close all but one owner, then use that reserved success closure to announce streams.
A producer failure instead cancels all descendants. Every owner ref is initially announced;
repeated owner descriptors are allowed.
-/
theorem sharedDeferredStreams_completeRun_with_owners
    {paths bound roles nodes path result children}
    (nonempty : nodes ≠ [])
    (onlyStreams : StreamOnly children)
    (coherent
      : MixedOwnerPaths.WorkAt paths bound
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    (roleCoherent
      : RefRoles.WorkRoles roles
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    (under
      : ExecutionPaths.WorkUnder []
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    (positive
      : ExecutionErrors.WorkPositive
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    : ∃ history,
        AdmissibleRun
          (.executionGroup (nodes.map (fun node => { node })) path result children)
          history
        ∧ ∀ node ∈ nodes,
            node.ref
            ∈ (history.initialGroups ++ history.initialStreams).map DeliveryNode.ref := by
  classical
  let work := Work.executionGroup (nodes.map (fun node => { node })) path result children
  have task : TaskAt work (.executionGroup []) (nodes.map DeliveryNode.ref) none
      (.object path result.deliveryResult) := by
    simpa only [List.map_map, Function.comp_def]
      using TaskAt.executionGroup
        (show Located work []
                (.executionGroup (nodes.map (fun node => { node })) path result children)
                none [] from .root)
  have root (node : DeliveryNode) (member : node ∈ nodes) : NodeAt work node .group [] none :=
    .group (group := { node }) .root (List.mem_map.mpr ⟨node, member, rfl⟩)
  have eligible (node : DeliveryNode) (member : node ∈ nodes)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
    refine ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨fun failure => failure.nonempty rfl, Or.inr ?_⟩, by simp, by simp⟩
    intro accounted
    rcases accounted (.executionGroup []) (nodes.map DeliveryNode.ref)
      ⟨none, .object path result.deliveryResult, task⟩ (List.mem_map.mpr ⟨node, member, rfl⟩)
      with cancelled | published
    · exact cancelled.nonempty rfl
    · simp [Published] at published
  obtain ⟨anchor, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have seed : Initializes work [anchor] [] := by
    refine ⟨⟨by simp, ?_, by simp⟩, by simp⟩
    intro node inSeed
    have same := List.mem_singleton.mp inSeed
    subst node
    exact ⟨[], none, root anchor member, eligible anchor member⟩
  obtain ⟨groups, streams, initialized, covers⟩ := seed.covering_exists
  have rootNotified (node : DeliveryNode) (member : node ∈ nodes)
      : node.ref ∈ (groups ++ streams).map DeliveryNode.ref :=
    covers node .group [] none (root node member) (eligible node member)
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    initialized.emptyExplains _
  have opened : Open ((groups ++ streams).map DeliveryNode.ref) [] anchor.ref := by
    exact ⟨by simpa [announcedRefs, pendingRefs] using rootNotified anchor member,
      by simp [completedRefs]⟩
  have anchorOwner : anchor.ref ∈ nodes.map DeliveryNode.ref :=
    List.mem_map.mpr ⟨anchor, member, rfl⟩
  cases outcome : result.deliveryResult with
  | error errors =>
      rw [outcome] at task
      have recorded := initial.record_failure task rfl (.root ⟨_, _, task⟩)
        ⟨anchor.ref, anchorOwner, opened⟩ (fun cancelled => cancelled.nonempty rfl)
      have accounted : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload →
          TaskAccounted work (fun _ => .executionGroup []) []
            [(0, .executionGroup [])] occurrence := by
        intro occurrence owners producer payload known
        apply Or.inl
        apply all_tasks_cancelled_of_roots (by simp [Published]) (known := known)
        intro occurrence owners payload rootTask
        have same := deferredStreams_root_task onlyStreams rootTask
        subst occurrence
        exact TaskCancelled.of_recorded task
          (by intro empty; exact nonempty (List.map_eq_nil_iff.mp empty))
          (by simp [Published])
          (by simp [failedBefore])
      have supported : OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref)
          (fun _ => .executionGroup []) [] [(0, .executionGroup [])] := by
        intro ref active _
        obtain ⟨node, kind, parents, birth, descriptor, same, available⟩ :=
          Explains.announced_producer_available initial active.1
        cases kind with
        | group =>
            have member := (sharedDeferredStreams_group onlyStreams descriptor).2.2
            have contributes : ref ∈ nodes.map DeliveryNode.ref :=
              List.mem_map.mpr ⟨node, member, same⟩
            exact ⟨
              errors,
              .of_task task (by simp [failedBefore]) contributes rfl
                (by
                  simpa only [Payload.failure, Option.getD_some]
                    using positive.task task rfl)
            ⟩
        | stream =>
            obtain ⟨address, items, located⟩ := descriptor
            rcases deferredStreams_located onlyStreams located with
              ⟨_, impossible, _, _⟩ | ⟨_, nonroot, _⟩
            · cases impossible
            · cases birth with
              | none => exact False.elim (nonroot rfl)
              | some source => simpa [Published] using available source rfl
      obtain ⟨closures, _, _, finished, allClosed⟩ := recorded.close_open_refs supported accounted
        (announcedRefs ((groups ++ streams).map DeliveryNode.ref) [])
        (fun _ opened => opened.1)
      have positiveCount : 0 < errors := by
        simpa only [Payload.failure, Option.getD_some] using positive.task task rfl
      have openOwner : ∃ ref ∈ nodes.map DeliveryNode.ref,
          Open ((groups ++ streams).map DeliveryNode.ref)
            (([] ++ closures).take 0) ref :=
        ⟨anchor.ref, anchorOwner, by simpa using opened⟩
      have reported := Explains.recorded_task_reported coherent finished allClosed
        (cut := 0) (by simp) task positiveCount openOwner
      have localWork : ExecutionPaths.WorkUnder path work :=
        ⟨⟨[], by simp⟩, under.2⟩
      obtain ⟨tail, run, _, _⟩ := (WorkBatching.singletons ([] ++ closures)).finish_accounted
        finished (fun ref active _ => (active.2 (allClosed ref active.1)).elim)
        (fun occurrence owners producer payload known =>
          (accounted occurrence owners producer payload known).append closures)
        (fun occurrence owners producer payload known _ =>
          reported.descendant (localWork.task_under known))
      exact ⟨_, run, rootNotified⟩
  | ok value =>
      obtain ⟨data, errors⟩ := value
      rw [outcome] at task
      have ready : CanPublish work (fun _ => .executionGroup []) [] [] (.executionGroup []) none :=
        ⟨by simp [Published], fun cancelled => cancelled.nonempty rfl, by simp, trivial⟩
      obtain ⟨owner, selectedOwner⟩ := owner_exists_of_available coherent task
        ⟨anchor, ⟨⟨.group, [], none, root anchor member⟩, anchorOwner, opened⟩,
          fun failure => failure.nonempty rfl⟩
      let event := WorkQueueEvent.groupValues owner [{ path, data, errors }]
      let matching := matchNext (fun _ => .executionGroup []) 0 (.executionGroup [])
      have published : Explains work groups streams [event] matching [] :=
        initial.publish_object task ready selectedOwner
      have deferred : DeferredTasksAccounted work matching [event] [] := by
        intro address owners producer payload known
        have same := (deferredStreams_deferred_task onlyStreams known).1
        subst address
        exact Or.inr (published_matchNext (event := event) trivial
          (fun _ => .executionGroup []) [] (.executionGroup []))
      have accounted (ref : NodeRef) (inRefs : ref ∈ nodes.map DeliveryNode.ref)
          : NodeAccounted work matching [event] [] ref := by
        obtain ⟨node, inNodes, rfl⟩ := List.mem_map.mp inRefs
        rintro occurrence owners ⟨producer, payload, known⟩ contributes
        cases StructuralEquivalence.taskAt_of_current known with
        | executionGroup located => exact deferred _ _ _ _ known
        | item located entry =>
            exact False.elim (stream_group_refs_distinct roleCoherent
              (NodeAt.stream located.toCurrent) (root node inNodes)
              (List.mem_singleton.mp contributes).symm)
      let others := (nodes.map DeliveryNode.ref).filter (fun ref => ref != anchor.ref)
      obtain ⟨closures, _, _, closedOthers, completedOthers, selected⟩ :=
        published.close_accounted_refs
          (Explains.openFailureCauses_of_healthy_groups positive published
            (fun node dependencies birth descriptor =>
              sharedDeferredStreams_success_groups_healthy onlyStreams roleCoherent published
                outcome descriptor)) others
          (by
            intro ref inOthers
            obtain ⟨node, inNodes, rfl⟩ := List.mem_map.mp (List.mem_filter.mp inOthers).1
            simpa [announcedRefs, pendingRefs, event, eventPending]
              using rootNotified node inNodes)
          (fun ref inOthers => accounted ref (List.mem_filter.mp inOthers).1)
      have anchorOpen : Open ((groups ++ streams).map DeliveryNode.ref) [event] anchor.ref := by
        simpa [Open, announcedRefs, pendingRefs, completedRefs, event, eventPending,
          eventCompleted]
          using opened
      have reserved := anchorOpen.append_unselected selected (by simp [others])
      have dependenciesClosed {newGroups newStreams : List DeliveryNode}
          : StreamDependenciesCompleted work
              ([event] ++ closures ++ [.groupSuccess anchor newGroups newStreams]) := by
        intro stream dependencies producer known ref inDependencies
        rcases deferredStreams_stream_dependencies onlyStreams known with rfl | rfl
        · cases inDependencies
        · have inRefs : ref ∈ nodes.map DeliveryNode.ref := by
            simpa only [List.map_map, Function.comp_def] using inDependencies
          by_cases same : ref = anchor.ref
          · simp [completedRefs, eventCompleted, same]
          · have other : ref ∈ others := List.mem_filter.mpr
              ⟨inRefs, by simpa using same⟩
            have previous := completedOthers ref other
            simpa only [completedRefs, List.flatMap_append]
              using List.mem_append_left
                (completedRefs [.groupSuccess anchor newGroups newStreams]) previous
      obtain ⟨newGroups, newStreams, released, notified⟩ :=
        closedOthers.complete_group_streams_notified (root anchor member) reserved
          (fun failure => failure.nonempty rfl)
          ((accounted anchor.ref anchorOwner).append closures)
          dependenciesClosed
      have preserved := (deferred.extend (List.Subset.refl []) closures).extend
        (List.Subset.refl []) [.groupSuccess anchor newGroups newStreams]
      obtain ⟨tail, run⟩ := released_streams_run_extension_of_healthy_groups coherent under
        positive (fun outputs next cuts explanation node dependencies birth descriptor =>
          sharedDeferredStreams_success_groups_healthy onlyStreams roleCoherent explanation
            outcome descriptor) released preserved dependenciesClosed notified
        (WorkBatching.singletons _)
      exact ⟨_, run, rootNotified⟩

/-- A shared deferred producer has a complete run with local stream-only descendants and
positive failures. Witness: forget the stronger construction's initial coverage of every
owner ref, retaining the actual reports for unpublished attachments.
-/
theorem sharedDeferredStreams_completeRun_exists
    {paths bound roles nodes path result children}
    (nonempty : nodes ≠ [])
    (onlyStreams : StreamOnly children)
    (coherent
      : MixedOwnerPaths.WorkAt paths bound
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    (roleCoherent
      : RefRoles.WorkRoles roles
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    (under
      : ExecutionPaths.WorkUnder []
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    (positive
      : ExecutionErrors.WorkPositive
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    : ∃ history,
        AdmissibleRun
          (.executionGroup (nodes.map (fun node => { node })) path result children)
          history := by
  obtain ⟨history, run, _⟩ := sharedDeferredStreams_completeRun_with_owners nonempty
    onlyStreams coherent roleCoherent under positive
  exact ⟨history, run⟩

/-- The single-owner deferred-stream result is a special case of shared-owner existence.
Witness: instantiate the nonempty owner list with one node; local attachments and positive
failures are retained, and no terminal history is supplied.
-/
theorem deferredStreams_completeRun_exists
    {paths bound roles node path result children}
    (onlyStreams : StreamOnly children)
    (coherent
      : MixedOwnerPaths.WorkAt paths bound
          (.executionGroup [{ node }] path result children))
    (roleCoherent
      : RefRoles.WorkRoles roles (.executionGroup [{ node }] path result children))
    (under
      : ExecutionPaths.WorkUnder [] (.executionGroup [{ node }] path result children))
    (positive
      : ExecutionErrors.WorkPositive (.executionGroup [{ node }] path result children))
    : ∃ history,
        AdmissibleRun (.executionGroup [{ node }] path result children) history := by
  exact sharedDeferredStreams_completeRun_exists (nodes := [node]) (by simp)
    onlyStreams coherent roleCoherent under positive

end GraphQL.IncrementalDelivery.Correctness
