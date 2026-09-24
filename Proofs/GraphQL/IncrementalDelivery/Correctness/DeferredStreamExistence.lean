import Proofs.GraphQL.IncrementalDelivery.Correctness.NestedStreamExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles

/-! A deferred producer can release arbitrarily nested stream-only child work.
Both producer outcomes admit complete runs; no output history is supplied as a premise.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Structural facts for one deferred producer and its stream descendants
-----------------------------------------------------------------------------------------

/-- Below a single deferred producer, locations are stream-only, have a producer, and
retain either its shared defer keys or no enclosing keys. Witness: structural navigation;
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
          ∧ (owners = [] ∨ owners = fragments.map (fun group => group.node.key))) := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | left _ ih =>
      rcases ih with ⟨_, impossible, _, _⟩ | ⟨only, birth, owners⟩
      · cases impossible
      · rw [StreamOnly] at only
        exact Or.inr ⟨only.1, birth, owners⟩
  | right _ ih =>
      rcases ih with ⟨_, impossible, _, _⟩ | ⟨only, birth, owners⟩
      · cases impossible
      · rw [StreamOnly] at only
        exact Or.inr ⟨only.2, birth, owners⟩
  | executionGroup _ ih =>
      rcases ih with ⟨rfl, same, rfl, rfl⟩ | ⟨impossible, _, _⟩
      · cases same
        exact Or.inr ⟨onlyStreams, by simp, Or.inr rfl⟩
      · simp only [StreamOnly] at impossible
  | item _ entry ih =>
      rcases ih with ⟨_, impossible, _, _⟩ | ⟨only, _, _⟩
      · cases impossible
      · rw [StreamOnly] at only
        exact Or.inr ⟨only _ (List.mem_of_getElem? entry), by simp, Or.inl rfl⟩

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
      ∧ owners = fragments.map (fun group => group.node.key)
      ∧ producer = none
      ∧ payload = .object path result := by
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
    : dependencies = [] ∨ dependencies = fragments.map (fun group => group.node.key) := by
  obtain ⟨address, items, located⟩ := known
  rcases deferredStreams_located onlyStreams located with
    ⟨_, impossible, _, _⟩ | ⟨_, _, owners⟩
  · cases impossible
  · exact owners

-----------------------------------------------------------------------------------------
-- Construct the deferred publication/closure or the justified failure
-----------------------------------------------------------------------------------------

/-- A shared deferred producer with dependency-free owners and stream-only children admits a
complete run for every producer/item outcome. Witness: announce the owner keys, publish
once, close all but one owner, then use that reserved success closure to announce streams.
A producer failure instead cancels all descendants. Every owner key is initially announced;
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
      : KeyRoles.WorkRoles roles
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    : ∃ history,
        AdmissibleRun
          (.executionGroup (nodes.map (fun node => { node })) path result children)
          history
        ∧ ∀ node ∈ nodes,
            node.key
            ∈ (history.initialGroups ++ history.initialStreams).map DeliveryNode.key := by
  classical
  let work := Work.executionGroup (nodes.map (fun node => { node })) path result children
  have task : TaskAt work (.executionGroup []) (nodes.map DeliveryNode.key) none
      (.object path result) := by
    simpa only [List.map_map, Function.comp_def]
      using TaskAt.executionGroup
        (show Located work []
                (.executionGroup (nodes.map (fun node => { node })) path result children)
                none [] from .root)
  have root (node : DeliveryNode) (member : node ∈ nodes) : NodeAt work node .group [] none :=
    .group (group := { node }) .root (List.mem_map.mpr ⟨node, member, rfl⟩)
  have eligible (node : DeliveryNode) (member : node ∈ nodes)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
    refine ⟨by simp [announcedKeys, pendingKeys], fun failure => failure.nonempty rfl,
      Or.inr ?_, by simp, by simp⟩
    intro accounted
    rcases accounted (.executionGroup []) (nodes.map DeliveryNode.key)
      ⟨none, .object path result, task⟩ (List.mem_map.mpr ⟨node, member, rfl⟩)
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
      : node.key ∈ (groups ++ streams).map DeliveryNode.key :=
    covers node .group [] none (root node member) (eligible node member)
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  have opened : Open ((groups ++ streams).map DeliveryNode.key) [] anchor.key := by
    exact ⟨by simpa [announcedKeys, pendingKeys] using rootNotified anchor member,
      by simp [completedKeys]⟩
  have anchorOwner : anchor.key ∈ nodes.map DeliveryNode.key :=
    List.mem_map.mpr ⟨anchor, member, rfl⟩
  cases result with
  | error errors =>
      have recorded := initial.record_failure task rfl (.root ⟨_, _, task⟩)
        ⟨anchor.key, anchorOwner, opened⟩ (fun cancelled => cancelled.nonempty rfl)
      have accounted : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload →
          Accounted work (fun _ => .executionGroup []) []
            (failedBefore [(0, .executionGroup [])] 0) occurrence := by
        intro occurrence owners producer payload known
        apply Or.inl
        apply all_tasks_cancelled_of_roots (known := known)
        intro occurrence owners payload rootTask
        have same := deferredStreams_root_task onlyStreams rootTask
        subst occurrence
        exact TaskCancelled.of_recorded task
          (by intro empty; exact nonempty (List.map_eq_nil_iff.mp empty))
          (by simp [failedBefore])
      obtain ⟨tail, run, _, _⟩ := WorkBatching.nil.finish_accounted recorded accounted
      exact ⟨_, run, rootNotified⟩
  | ok value =>
      obtain ⟨data, errors⟩ := value
      have ready : CanPublish work (fun _ => .executionGroup []) [] [] (.executionGroup []) none :=
        ⟨by simp [Published], fun cancelled => cancelled.nonempty rfl, by simp, trivial⟩
      obtain ⟨owner, selectedOwner⟩ := owner_exists_of_available coherent task
        ⟨anchor, ⟨.group, [], none, root anchor member⟩, anchorOwner, opened,
          fun failure => failure.nonempty rfl⟩
      let event := WorkEvent.groupValues owner [{ path, data, errors }]
      let matching := matchNext (fun _ => .executionGroup []) 0 (.executionGroup [])
      have published : Explains work groups streams [event] matching [] :=
        initial.publish_object task ready selectedOwner
      have deferred : DeferredTasksAccounted work matching [event] [] := by
        intro address owners producer payload known
        have same := (deferredStreams_deferred_task onlyStreams known).1
        subst address
        exact Or.inr (published_matchNext (event := event) trivial
          (fun _ => .executionGroup []) [] (.executionGroup []))
      have accounted (key : Nat) (inKeys : key ∈ nodes.map DeliveryNode.key)
          : NodeAccounted work matching [event] [] key := by
        obtain ⟨node, inNodes, rfl⟩ := List.mem_map.mp inKeys
        rintro occurrence owners ⟨producer, payload, known⟩ contributes
        cases StructuralEquivalence.taskAt_of_current known with
        | executionGroup located => exact deferred _ _ _ _ known
        | item located entry =>
            exact False.elim (stream_group_keys_distinct roleCoherent
              (NodeAt.stream located.toCurrent) (root node inNodes)
              (List.mem_singleton.mp contributes).symm)
      let others := (nodes.map DeliveryNode.key).filter (fun key => key != anchor.key)
      obtain ⟨closures, _, _, closedOthers, completedOthers, selected⟩ :=
        published.close_accounted_keys others
          (by
            intro key inOthers
            obtain ⟨node, inNodes, rfl⟩ := List.mem_map.mp (List.mem_filter.mp inOthers).1
            simpa [announcedKeys, pendingKeys, event, eventPending]
              using rootNotified node inNodes)
          (fun key inOthers => accounted key (List.mem_filter.mp inOthers).1)
      have anchorOpen : Open ((groups ++ streams).map DeliveryNode.key) [event] anchor.key := by
        simpa [Open, announcedKeys, pendingKeys, completedKeys, event, eventPending,
          eventCompleted]
          using opened
      have reserved := anchorOpen.append_unselected selected (by simp [others])
      have dependenciesClosed {newGroups newStreams : List DeliveryNode}
          : StreamDependenciesCompleted work
              ([event] ++ closures ++ [.groupSuccess anchor newGroups newStreams]) := by
        intro stream dependencies producer known key inDependencies
        rcases deferredStreams_stream_dependencies onlyStreams known with rfl | rfl
        · cases inDependencies
        · have inKeys : key ∈ nodes.map DeliveryNode.key := by
            simpa only [List.map_map, Function.comp_def] using inDependencies
          by_cases same : key = anchor.key
          · simp [completedKeys, eventCompleted, same]
          · have other : key ∈ others := List.mem_filter.mpr
              ⟨inKeys, by simpa using same⟩
            have previous := completedOthers key other
            simpa only [completedKeys, List.flatMap_append]
              using List.mem_append_left
                (completedKeys [.groupSuccess anchor newGroups newStreams]) previous
      obtain ⟨newGroups, newStreams, released, notified⟩ :=
        closedOthers.complete_group_streams_notified (root anchor member) reserved
          (fun failure => failure.nonempty rfl)
          (by simpa [failedBefore] using (accounted anchor.key anchorOwner).append closures)
          dependenciesClosed
      have preserved := (deferred.extend (List.Subset.refl []) closures).extend
        (List.Subset.refl []) [.groupSuccess anchor newGroups newStreams]
      obtain ⟨tail, run⟩ := released_streams_run_extension coherent released preserved
        dependenciesClosed notified (WorkBatching.singletons _)
      exact ⟨_, run, rootNotified⟩

/-- A shared deferred producer has a complete run with arbitrary stream-only descendants.
Witness: forget the stronger construction's initial coverage of every owner key.
-/
theorem sharedDeferredStreams_completeRun_exists
    {paths bound roles nodes path result children}
    (nonempty : nodes ≠ [])
    (onlyStreams : StreamOnly children)
    (coherent
      : MixedOwnerPaths.WorkAt paths bound
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    (roleCoherent
      : KeyRoles.WorkRoles roles
          (.executionGroup (nodes.map (fun node => { node })) path result children))
    : ∃ history,
        AdmissibleRun
          (.executionGroup (nodes.map (fun node => { node })) path result children)
          history := by
  obtain ⟨history, run, _⟩ := sharedDeferredStreams_completeRun_with_owners nonempty
    onlyStreams coherent roleCoherent
  exact ⟨history, run⟩

/-- The single-owner deferred-stream result is a special case of shared-owner existence.
Witness: instantiate the nonempty owner list with one node; producer and item outcomes
remain unrestricted, and no terminal history is supplied.
-/
theorem deferredStreams_completeRun_exists
    {paths bound roles node path result children}
    (onlyStreams : StreamOnly children)
    (coherent
      : MixedOwnerPaths.WorkAt paths bound
          (.executionGroup [{ node }] path result children))
    (roleCoherent
      : KeyRoles.WorkRoles roles (.executionGroup [{ node }] path result children))
    : ∃ history,
        AdmissibleRun (.executionGroup [{ node }] path result children) history := by
  exact sharedDeferredStreams_completeRun_exists (nodes := [node]) (by simp)
    onlyStreams coherent roleCoherent

end GraphQL.IncrementalDelivery.Correctness
