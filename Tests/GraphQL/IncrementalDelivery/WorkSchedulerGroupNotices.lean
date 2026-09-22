import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPruningNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeDependencies
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublishedMemberships
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCarrierNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshGroupPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFrontierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PruningBudget
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPathCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SupportedAncestorPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Pruning promotes real contributors and retains buffered values or cached failures. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerGroupNotices
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := { key := 0, path := [], label := some (.string "P") }
private def child : DeliveryNode := { key := 1, path := [], label := some (.string "C") }
private def occurrence : Occurrence := .executionGroup [1, 0]

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨child, [parent]⟩] [] (.ok ([("a", .scalar "a")], 0))
        (.combine .empty .empty))
      .empty)

private def parentRecord : GroupNode :=
  { group := ⟨parent, none⟩, childGroups := [child.key] }

private def childRecord : GroupNode :=
  { group := ⟨child, some parent.key⟩, tasks := [occurrence], pending := 1 }

private def queue : State :=
  {
    registeredGroups := [parent.key, child.key],
    groupNodes := [parentRecord, childRecord],
    tasks := [⟨occurrence, [child]⟩]
  }

private theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [defer [field "a"] (some "C")] (some "P")], ?_⟩
  cbv

private theorem childKnown : NodeAt work child .group [parent.key] none :=
  .group (address := [1, 0]) (groups := [⟨child, [parent]⟩])
    (path := []) (result := .ok ([("a", .scalar "a")], 0))
    (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self

private theorem parentKnown : GroupRecordAt work parent [] := by
  refine ⟨[1, 0], [⟨child, [parent]⟩], [], .ok ([("a", .scalar "a")], 0),
    .combine .empty .empty, none, [], ⟨child, [parent]⟩, [], rfl,
    List.mem_cons_self, ?_, rfl⟩
  exact ⟨[child], rfl⟩

/-- Initialization covers C after pruning its taskless parent P.
Witness: the general generated initial-coverage theorem supplies the actual active root;
the concrete checks establish that P is absent while C survives.
-/
theorem taskless_initial_group_covered
    : let initial := State.initialize (Work.fromExecution work)
      initial.groupNode? parent.key = none
      ∧ ∃ root ∈ initial.rootGroups, initial.LiveDescendant root child.key := by
  intro initial
  refine ⟨by cbv, generated.initial_live_group_root_coverage child.key ?_⟩
  exact ⟨childRecord, by cbv⟩

private theorem childRecordKnown : GroupRecordAt work child [parent.key] := by
  refine ⟨[1, 0], [⟨child, [parent]⟩], [], .ok ([("a", .scalar "a")], 0),
    .combine .empty .empty, none, [], ⟨child, [parent]⟩, [parent], rfl,
    List.mem_cons_self, ?_, rfl⟩
  exact ⟨[], rfl⟩

private theorem registry : queue.GroupNodesMatchWork work := by
  intro node member
  rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
    with rfl | rfl
  · exact ⟨[], parentKnown⟩
  · exact ⟨[parent.key], childRecordKnown⟩

private theorem support
    : queue.GroupKeySupport
        (fun key =>
          ∃ dependencies, NodeHasDependencies work key .group dependencies) := by
  constructor
  · intro node member absent
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
      with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact False.elim (absent ⟨[parent.key], child, none, childKnown, rfl⟩)
  · intro key member
    cases member

/-- Child-first repeated registration still connects the live child to its parent.
Witness: the general two-pass completeness theorem on an empty registry, followed by
the actual lookups. Neither parent-first input nor deduplicated input is assumed.
-/
theorem child_first_registration_links
    : let groups := [childRecord.group, parentRecord.group, childRecord.group]
      let registered := (({} : State).addGroups groups).1
      ∃ node,
        registered.groupNode? parent.key = some node ∧ child.key ∈ node.childGroups := by
  intro groups registered
  let parents : Nat → Keys := fun key => if key = child.key then [parent.key] else []
  have complete : ({} : State).ParentLinksComplete parents := by
    intro node member
    cases member
  have canonical : ∀ group ∈ groups, group.parent = (parents group.node.key).head? := by
    intro group member
    rcases (show group = childRecord.group ∨ group = parentRecord.group
        ∨ group = childRecord.group from by simpa [groups] using member)
      with rfl | rfl | rfl <;> decide
  have linked := complete.addGroups (by simp [State.GroupKeysUnique])
    (by intro node member; cases member) (by intro key member; cases member) groups canonical
  have parentFound : registered.groupNode? parent.key = some parentRecord := by cbv
  have childFound : registered.groupNode? child.key = some { group := childRecord.group } := by cbv
  exact ⟨
    parentRecord,
    parentFound,
    linked _ (List.mem_of_find?_eq_some childFound)
      _ (List.mem_of_find?_eq_some parentFound) (by decide)
  ⟩

/-- Live child paths retain the dependency of a taskless registration ancestor.
Witness: canonical record links and generated ancestry recover P from the path P to C;
the generic path theorem does not require P to have a contributing task.
-/
theorem taskless_path_retains_ancestor : parent.key ∈ [parent.key] := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have links : queue.ChildLinksCanonical parents := by
    intro node member key childMember
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
      with rfl | rfl
    · obtain rfl := List.mem_singleton.mp childMember
      rw [← canonical _ _ childRecordKnown]
      rfl
    · cases childMember
  have path : queue.LiveDescendant parent.key child.key :=
    .child (by rfl) List.mem_cons_self (.self (by rfl))
  rcases path.ancestor_or_self generated registry links canonical childRecordKnown rfl with
    same | ancestor
  · contradiction
  · exact ancestor

/-- A real nested-defer query registers a taskless parent but announces only its child.
Witness: evaluate the actual integration, pruning, and initialization boundaries; the
parent is a registration descriptor, not a fabricated contributing work node.
-/
theorem taskless_parent_promoted
    : (({} : State).maybeIntegrateWork (Work.fromExecution work))
        = (queue, ⟨[parent], []⟩)
      ∧ (queue.pruneEmptyGroups [parent]).2 = [child]
      ∧ (State.initialize (Work.fromExecution work)).initialGroups = [child] := by
  exact ⟨by cbv, by cbv, by cbv⟩

/-- Initial taskless-shell promotion cannot duplicate the announced child's key.
Witness: generated initialization applies the generic unique-frontier pruning theorem,
not evaluation of the final singleton notice list.
-/
theorem taskless_initial_notices_unique
    : ((State.initialize (Work.fromExecution work)).initialGroups.map
        DeliveryNode.key).Nodup :=
  generated.initialGroups_unique

/-- The taskless ancestor cannot exhaust pruning fuel or hide its surviving child.
Witness: generic budget independence and converse path coverage, with the concrete
generated registration frontier. Neither conclusion assumes the child's returned notice.
-/
theorem taskless_pruning_complete (extra : Nat)
    : State.pruneEmptyGroups.go (queue.groupNodes.length + 1 + 1 + extra)
          queue [parent] []
        = queue.pruneEmptyGroups [parent]
      ∧ ∃ root ∈ (queue.pruneEmptyGroups [parent]).2,
          (queue.pruneEmptyGroups [parent]).1.LiveDescendant root.key child.key := by
  let parents : Nat → Keys := fun _ => [parent.key]
  have links : queue.ChildLinksCanonical parents := by
    intro node member key linked
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
      with rfl | rfl
    · rfl
    · cases linked
  have children : queue.ChildGroupsUnique := by
    intro node member
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
      with rfl | rfl <;> simp [parentRecord, childRecord]
  have frontier : queue.GroupFrontier [parent] := by
    intro group member node live
    obtain rfl := List.mem_singleton.mp member
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using live)
      with rfl | rfl <;> decide
  have unique : ([parent].map DeliveryNode.key).Nodup := by simp
  have live : ∀ group ∈ [parent], ∃ node, queue.groupNode? group.key = some node := by
    intro group member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨parentRecord, rfl⟩
  refine ⟨
    State.pruneEmptyGroups_budget_complete links children frontier unique live extra,
    State.pruneEmptyGroups_surviving_descendant links children frontier unique live ?_ ?_
  ⟩
  · exact ⟨parent, List.mem_cons_self,
      .child (by rfl) List.mem_cons_self (.self (by rfl))⟩
  · exact ⟨childRecord, by cbv⟩

/-- Successful release preserves uniqueness across taskless branches and stale child links.
Witness: the generic release theorem uses only canonical links and unique child lists;
this local transition regression supplies those finite structural premises directly.
-/
theorem taskless_branched_release_unique
    : let closing : GroupNode := { parentRecord with childGroups := [1, 99, 3] }
      let shell : GroupNode :=
        { childRecord with tasks := [], pending := 0, childGroups := [2] }
      let left : GroupNode :=
        { group := ⟨⟨2, [], none⟩, some 1⟩, tasks := [occurrence], pending := 1 }
      let right : GroupNode :=
        { group := ⟨⟨3, [], none⟩, some 0⟩, tasks := [occurrence], pending := 1 }
      let current : State := { groupNodes := [closing, shell, left, right] }
      (((current.finishGroupSuccess closing).2.2.newGroups).map
        DeliveryNode.key).Nodup := by
  intro closing shell left right current
  let parents : Nat → Keys := fun key => if key = 2 then [1] else [0]
  apply current.finishGroupSuccess_newGroups_unique (parents := parents)
  · intro node member key linked
    simp only [current, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · simp only [closing, List.mem_cons, List.not_mem_nil, or_false] at linked
      rcases linked with rfl | rfl | rfl <;> rfl
    · obtain rfl := List.mem_singleton.mp linked
      rfl
    · cases linked
    · cases linked
  · intro node member
    simp only [current, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [closing, shell, left, right]
  · exact List.mem_cons_self

/-- Successful closure retains coverage through a taskless branch and a stale child link.
Witness: the generic close-and-activate theorem covers both promoted leaves and a separate
old root. The regression checks path coverage, not merely that notice keys are distinct.
-/
theorem branched_release_covers_survivors
    : let closing : GroupNode := { parentRecord with childGroups := [1, 99, 3] }
      let shell : GroupNode :=
        { childRecord with tasks := [], pending := 0, childGroups := [2] }
      let left : GroupNode :=
        { group := ⟨⟨2, [], none⟩, some 1⟩, tasks := [occurrence], pending := 1 }
      let right : GroupNode :=
        { group := ⟨⟨3, [], none⟩, some 0⟩, tasks := [occurrence], pending := 1 }
      let separate : GroupNode :=
        { group := ⟨⟨9, [], none⟩, none⟩, tasks := [occurrence], pending := 1 }
      let current : State :=
        { rootGroups := [0, 9], groupNodes := [closing, shell, left, right, separate] }
      let result := current.finishGroupSuccess closing
      let next := result.1.startNewWork result.2.2
      ∀ key ∈ [2, 3, 9], ∃ root ∈ next.rootGroups, next.LiveDescendant root key := by
  intro closing shell left right separate current result next key member
  let parents : Nat → Keys := fun key => if key = 2 then [1] else [0]
  have links : current.ChildLinksCanonical parents := by
    intro node member key linked
    simp only [current, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · simp only [closing, List.mem_cons, List.not_mem_nil, or_false] at linked
      rcases linked with rfl | rfl | rfl <;> rfl
    · obtain rfl := List.mem_singleton.mp linked
      rfl
    · cases linked
    · cases linked
    · cases linked
  have children : current.ChildGroupsUnique := by
    intro node member
    simp only [current, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [closing, shell, left, right, separate]
  have forest : current.RemovalForest parents := by
    refine ⟨children, links, ?_⟩
    intro first second firstMember secondMember linked
    simp only [current, List.mem_cons, List.not_mem_nil, or_false] at firstMember secondMember
    rcases firstMember with rfl | rfl | rfl | rfl | rfl <;>
      rcases secondMember with rfl | rfl | rfl | rfl | rfl <;>
      simp [closing, shell, left, right, separate, parentRecord, parent, childRecord, child]
        at linked ⊢
  apply State.finishGroupSuccess_root_coverage forest (group := closing) (by rfl)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨0, List.mem_cons_self,
        .child (by rfl) List.mem_cons_self
          (.child (by rfl) List.mem_cons_self (.self (by rfl)))⟩
    · exact ⟨0, List.mem_cons_self,
        .child (by rfl) (by decide) (.self (by rfl))⟩
    · exact ⟨9, by decide, .self (by rfl)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨left, by cbv⟩
    · exact ⟨right, by cbv⟩
    · exact ⟨separate, by cbv⟩

/-- Pruning a fresh taskless wrapper preserves an earlier root, even if that root is empty.
Witness: registration isolates fresh child paths from old keys. The new wrapper really is
removed, so this regression cannot be discharged by assuming that pruning does nothing.
-/
theorem taskless_item_preserves_old_root
    : let before : State :=
        {
          rootGroups := [9],
          registeredGroups := [9],
          groupNodes := [{ group := ⟨⟨9, [], none⟩, none⟩ }]
        }
      let item : StreamItem := ⟨.item [] 0, ⟨.object [], 0⟩, Work.fromExecution work⟩
      (before.integrateStreamItem item).RootGroupsPresent
      ∧ (before.integrateStreamItem item).rootGroups = [9, child.key]
      ∧ (before.integrateStreamItem item).groupNode? parent.key = none := by
  intro before item
  refine ⟨
    State.RootGroupsPresent.integrateStreamItem_registered ?_ ?_ ?_ item,
    by cbv,
    by cbv
  ⟩
  · intro key member
    exact member
  · intro node member
    obtain rfl := List.mem_singleton.mp member
    exact List.mem_cons_self
  · simp [State.GroupKeysUnique, before]

/-- Fresh taskless promotion preserves an existing root-to-child path, not just its root.
Witness: the generic item-integration coverage theorem; the old two-record branch is
disjoint from the new wrapper and child, and remains connected after that wrapper is pruned.
-/
theorem taskless_item_preserves_old_branch
    : let before : State :=
        {
          rootGroups := [9],
          registeredGroups := [9, 10],
          groupNodes :=
            [
              { group := ⟨⟨9, [], none⟩, none⟩, childGroups := [10] },
              { group := ⟨⟨10, [], none⟩, some 9⟩, tasks := [occurrence], pending := 1 }
            ]
        }
      let item : StreamItem := ⟨.item [] 0, ⟨.object [], 0⟩, Work.fromExecution work⟩
      ∃ root ∈ (before.integrateStreamItem item).rootGroups,
        (before.integrateStreamItem item).LiveDescendant root 10 := by
  intro before item
  refine State.integrateStreamItem_old_root_coverage
    (by simp [State.GroupKeysUnique, before]) ?_ item ?_
  · intro node member
    simp only [before, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · exact ⟨9, List.mem_cons_self, .child (by rfl) List.mem_cons_self (.self (by rfl))⟩

/-- The promoted child has its exact original descriptor and a live nonempty record.
Witness: the general pruning gate, applied to the generated integration state. The test
does not supply contributor provenance for the returned child as an output assumption.
-/
theorem promoted_notice_contents
    : (∃ dependencies producer, NodeAt work child .group dependencies producer)
      ∧ ∃ node,
          (queue.pruneEmptyGroups [parent]).1.groupNode? child.key = some node
          ∧ node.group.node = child
          ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true) := by
  apply queue.pruneEmptyGroups_noticeContents generated
    (by simp [State.GroupKeysUnique,
      queue, parentRecord, childRecord, parent, child])
    registry support [parent]
  · intro node member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨[], parentKnown⟩
  · rw [taskless_parent_promoted.2.1]
    exact List.mem_cons_self

/-- Promoting through a taskless ancestor preserves all of the child's dependency readiness.
Witness: instantiate the general inherited-readiness traversal with generated canonical
parent links. Only the removed parent needs silent accounting; the nonempty child does not.
-/
theorem promoted_notice_dependencies
    : ∀ key ∈ [parent.key],
        DependencySatisfied work [] (fun _ => occurrence) [] [] key := by
  have absent : ¬∃ producer, NodeHasProducer work parent.key producer := by
    rintro ⟨producer, node, kind, dependencies, known, same⟩
    have token := known.observationToken
    rw [same] at token
    simp [observationTokens, work, parent, child] at token
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have links : queue.ChildLinksCanonical parents := by
    intro node member key childMember
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
      with rfl | rfl
    · obtain rfl := List.mem_singleton.mp childMember
      rw [← canonical _ _ childRecordKnown]
      rfl
    · cases childMember
  apply queue.pruneEmptyGroups_dependenciesReady generated registry links canonical
    (groups := [parent]) (known := childKnown)
  · intro node member _ empty _
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
      with rfl | rfl
    · exact ⟨by simp [NodeFailed], .inl absent⟩
    · cases empty
  · intro group member key ancestor
    obtain rfl := List.mem_singleton.mp member
    rw [← canonical _ _ parentKnown] at ancestor
    cases ancestor
  · rw [taskless_parent_promoted.2.1]
    exact List.mem_cons_self

/-- The promoted notice is semantically eligible without announcing its taskless ancestor.
Witness: the ancestor has no structural node token, so its dependency is absent. The
concrete contents rule uses the child's real registered membership; neither cancellation
safety nor an unaccounted task is supplied as a premise. Initial admission is not assumed.
-/
theorem promoted_notice_eligible
    : CanAnnounce work [] (fun _ => occurrence) [] [] child .group [parent.key] none := by
  have task : TaskAt work occurrence [child.key] none
      (.object [] (.ok ([("a", .scalar "a")], 0))) :=
    .executionGroup (groups := [⟨child, [parent]⟩]) (children := .combine .empty .empty)
      (owners := []) (by cbv)
  have ready : ∀ key ∈ [parent.key],
      DependencySatisfied work [] (fun _ => occurrence) [] [] key := promoted_notice_dependencies
  refine State.groupNotice_canAnnounce_of_contents
    (queue := queue)
    (node := childRecord)
    generated
    (by intro index event selected; simp at selected)
    (by intro cut source member; cases member)
    childKnown
    (by simp [queue])
    (.inl (by simp [childRecord]))
    ?_ ?_ ?_
    (by simp [announcedKeys, pendingKeys])
    (by intro source impossible; cases impossible)
    ready ?_ ?_
  · intro node member other listed
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
      with rfl | rfl
    · cases listed
    · obtain rfl := List.mem_singleton.mp listed
      exact ⟨⟨occurrence, [child]⟩, by simp [queue], rfl, by simp [childRecord]⟩
  · intro actual member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨⟨[1, 0], _, none, rfl, task⟩, by cbv⟩
  · intro node member failed
    rcases (show node = parentRecord ∨ node = childRecord from by simpa [queue] using member)
      with rfl | rfl <;> cases failed
  · intro other listed source descriptor
    obtain rfl := List.mem_singleton.mp listed
    obtain ⟨otherOwners, payload, known⟩ := descriptor
    cases (task.unique known).2.1
  · intro other listed
    simp [Published]

/-- Zero pending tasks do not make a buffered value or cached error disappear.
Witness: direct pruning of the two local record forms; only a truly empty, error-free
shell is removable. This is a local transition regression, not a claimed source replay.
-/
theorem zero_pending_retained
    : let buffered : State := { groupNodes := [{ childRecord with pending := 0 }] }
      let failed : State :=
        {
          groupNodes :=
            [{ childRecord with tasks := [], pending := 0, failure := some 1 }]
        }
      (buffered.pruneEmptyGroups [child]).2 = [child]
      ∧ (failed.pruneEmptyGroups [child]).2 = [child] := by exact ⟨by cbv, by cbv⟩

-----------------------------------------------------------------------------------------
-- Both carrier kinds promote through taskless wrappers in actual source replay
-----------------------------------------------------------------------------------------

/-- A shared publication removes duplicate memberships from the surviving co-owner too.
Witness: the generic successful-flush theorem, instantiated with raw duplicate lists.
This is a local accounting check, not an assertion that malformed lists are generated.
-/
theorem shared_publication_clears_memberships
    : let closing : GroupNode := { parentRecord with tasks := [occurrence, occurrence] }
      let coowner : GroupNode := { childRecord with tasks := [occurrence, occurrence] }
      let task : TaskNode :=
        {
          task := ⟨occurrence, [parent, child]⟩,
          value :=
            some
              {
                deliveryGroups := [parent, child],
                path := [],
                data := [("a", .scalar "a")]
              }
        }
      let buffered : State := { groupNodes := [closing, coowner], taskNodes := [task] }
      (buffered.finishGroupSuccess closing).1.TaskMembershipAbsent occurrence := by
  dsimp only
  apply State.finishGroupSuccess_membershipAbsent
  · exact List.mem_cons_self
  · cbv

namespace GroupCarrier

private def selections : List Selection :=
  [defer [field "a", defer [defer [field "b"] (some "C")] (some "W")] (some "P")]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 50 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def child : DeliveryNode := { key := 2, path := [], label := some (.string "C") }

private def first : GraphEvent :=
  .taskSuccess occurrence
    { value := { deliveryGroups := [parent], path := [], data := [("a", .scalar "a")] } }

private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0, selections, rfl⟩

private theorem valid : ValidGraphEvents work [first] := by
  have known : TaskAt work occurrence [parent.key] none
      (.object [] (.ok ([("a", .scalar "a")], 0))) :=
    .executionGroup (groups := [⟨parent, []⟩]) (children := .combine .empty .empty)
      (owners := []) (by cbv)
  exact .append .nil ⟨_, _, known, by cbv, by cbv⟩
    (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
    ⟨_, _, _, known, by intro source impossible; cases impossible⟩

private def broken : State :=
  let initial := State.initialize (Work.fromExecution work)
  {
    initial with
      groupNodes := initial.groupNodes.filter (fun node => node.group.node.key != 1)
  }

private def liveParent : GroupNode :=
  { group := ⟨parent, none⟩, childGroups := [1], tasks := [occurrence], pending := 1 }

private def liveChild : GroupNode :=
  { group := ⟨child, some 1⟩, tasks := [.executionGroup [1, 1, 0]], pending := 1 }

private theorem broken_parent : broken.groupNode? parent.key = some liveParent := by cbv

private theorem broken_child : broken.groupNode? child.key = some liveChild := by cbv

private theorem broken_wrapper : broken.groupNode? 1 = none := by cbv

private theorem parent_task : TaskHasOwners work occurrence [parent.key] := by
  refine ⟨none, .object [] (.ok ([("a", .scalar "a")], 0)), ?_⟩
  exact .executionGroup (groups := [⟨parent, []⟩]) (children := .combine .empty .empty)
    (owners := []) (by cbv)

private theorem child_known : NodeAt work child .group [1, parent.key] none :=
  .group (address := [1, 1, 0])
    (groups := [⟨child, [⟨1, [], some (.string "W")⟩, parent]⟩])
    (path := []) (result := .ok ([("b", .scalar "b")], 0))
    (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self

/-- The generated initial queue connects P through taskless W to live C.
Witness: the general replay theorem at the empty prefix, not a manually supplied path.
-/
theorem initial_supported_path
    : (State.initialize (Work.fromExecution work)).LiveDescendant parent.key
        child.key := by
  have childFound : (State.initialize (Work.fromExecution work)).groupNode? child.key
      = some liveChild := by cbv
  have parentFound : (State.initialize (Work.fromExecution work)).groupNode? parent.key
      = some liveParent := by cbv
  exact generated.runNormalized_healthy_ancestor_path [] .nil rfl liveChild _ _ _ _
    childFound (groupRecordAt_of_nodeAt child_known) (fun invalid => invalid.nonempty rfl)
    (List.mem_cons_of_mem _ List.mem_cons_self) parent_task List.mem_cons_self
    ⟨liveParent, parentFound⟩

/-- Silently dropping W while P and C stay live would violate existing retirement evidence.
Witness: the generic supported-parent theorem forces the taskless intermediate W to remain
live below P's unsettled contribution. This tests the missing-parent obstruction directly;
the artificial deletion is not claimed to be an admitted implementation transition.
-/
theorem premature_wrapper_retirement_rejected
    : let initial := State.initialize (Work.fromExecution work)
      let broken : State :=
        {
          initial with
            groupNodes := initial.groupNodes.filter (fun node => node.group.node.key != 1)
        }
      ¬broken.HealthyRetiredAncestors work [] := by
  change ¬broken.HealthyRetiredAncestors work []
  intro retirement
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registry := createWorkQueue_parentRegistryClosed canonical
  have registered : broken.LiveGroupsRegistered := by
    intro node member
    exact (createWorkQueue_registration work).1 node (List.mem_filter.mp member).1
  have parentLive : ∃ node, broken.groupNode? 1 = some node :=
    retirement.supported_parent_present (queue := broken) (work := work)
      (child := liveChild) (parent := 1) (rest := [parent.key]) (ancestor := parent.key)
      registered registry canonical broken_child (groupRecordAt_of_nodeAt child_known)
      (fun invalid => invalid.nonempty rfl)
      (List.mem_cons_of_mem _ List.mem_cons_self) parent_task List.mem_cons_self
      ⟨liveParent, broken_parent⟩
  obtain ⟨node, found⟩ := parentLive
  rw [broken_wrapper] at found
  contradiction

/-- Closing P promotes C through its taskless wrapper, which is never announced.
Witness: exact generated replay; the general provenance theorem certifies the actual
carried child rather than relying on caller-supplied output metadata.
-/
theorem promoted_child_located
    : inputsStarted work [[first]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized [[first]]).2.flatten
        = [
          .groupValues parent
            [{
              path := [],
              data := [("a", .scalar "a")],
              errors := 0,
              deliveryGroups := [parent]
            }],
          .groupSuccess parent [child] []
        ]
      ∧ ∃ dependencies producer, NodeAt work child .group dependencies producer := by
  refine ⟨by cbv, by cbv, ?_⟩
  have noticed := createWorkQueue_runNormalized_atomicGroupNoticesLocated generated
    (inputs := [[first]]) valid (.groupSuccess parent [child] [])
    (by cbv; exact .tail _ (.head _))
  exact noticed child List.mem_cons_self

/-- The actual parent publication leaves no membership in any surviving group record.
Witness: legal generated replay derives a joint exact publication/removal inventory.
The nonempty output and sole source input identify the published occurrence, rather than
assuming that the implementation removed it or evaluating that conclusion directly.
-/
theorem published_parent_memberships_absent
    : ((State.initialize (Work.fromExecution work)).rawEventReplay
        [first]).1.TaskMembershipAbsent
        occurrence := by
  obtain ⟨published, values, inventory, absent⟩ :=
    createWorkQueue_rawEventReplay_publicationMemberships valid
  have nonempty : published ≠ [] := by
    intro empty
    rw [empty] at values
    cbv at values
    cases values
  obtain ⟨publication, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨result, source, _⟩ := inventory.provenance publication member
  have same : .taskSuccess publication.1 result = first := List.mem_singleton.mp source
  have occurrenceEq : publication.1 = occurrence := (GraphEvent.taskSuccess.inj same).1
  simpa only [occurrenceEq] using absent publication member

private def noticeBoundary : State :=
  let initial := State.initialize (Work.fromExecution work)
  let incoming : TaskNode := { task := ⟨occurrence, [parent]⟩ }
  let stored :=
    initial.putTaskNode
      {
        incoming with
          value :=
            some { path := [], data := [("a", .scalar "a")], deliveryGroups := [parent] }
      }
  let prepared := (stored.maybeIntegrateWork {} (some occurrence)).1
  (successGroupStep (prepared, [], {}) parent).1

/-- Promoted child contents exclude the parent's publication at the exact notice boundary.
Witness: generated metadata and the original mixed conformance ledger jointly recover
the emitting owner step, its retained child record, and membership exclusion. The child
is promoted through an empty wrapper; no record or contents premise is supplied by hand.
-/
theorem promoted_child_contents_on_common_witness
    : ∃ w : ConformancePlan.Witness,
      ∃ published : List ObjectPublication,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ObjectLedgerMatching work [[first]] w.events w.matching published
        ∧ ∃ node,
            noticeBoundary.groupNode? child.key = some node
            ∧ node.group.node = child
            ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
            ∧ ∀ publication ∈ published.take 1, publication.1 ∉ node.tasks := by
  have started : inputsStarted work [[first]] = true := by cbv
  obtain ⟨w, _, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated (inputs := [[first]]) valid started
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rwa [← inputsStarted_eq_batchesStarted])
  obtain ⟨steps, bounded, _, _, node, found, same, contents, excluded⟩ :=
    generated.taskSuccess_ownerNoticeContents (before := []) (after := [])
      (incoming := { task := ⟨occurrence, [parent]⟩ })
      (index := 1) (group := parent) (groups := [child]) (streams := [])
      covered valid (by cbv) (by cbv) (by cbv) List.mem_cons_self
  have zero : steps = 0 := by change steps < 1 at bounded; omega
  subst steps
  refine ⟨w, published, admitted, matching, node, found, same, contents, ?_⟩
  intro publication member
  apply excluded publication
  cbv
  cases published with
  | nil => simp at member
  | cons head tail =>
      have same : publication = head := by simpa using member
      subst publication
      exact .head _

/-- A promoted owner's child record is unpublished on the canonical atomic witness.
Witness: the general group-carrier theorem recovers the actual owner-fold boundary from
the selected second output; no explicit owner step or prefix count is supplied.
-/
theorem atomic_promoted_child_unpublished
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[1]? = some (.groupSuccess parent [child] [])
        ∧ RetainedNoticeContents work w.matching (w.events.take 1)
            (failedBefore w.failures 1) [first] child := by
  obtain ⟨w, history, _, _, _, _, _, streamReady, _, _, ledger, _, _, _, admitted,
    streamCuts, _, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_cuts generated
      (inputs := [[first]]) valid (by cbv)
  have selected : w.events[1]? = some (.groupSuccess parent [child] []) := by
    rw [history]
    cbv
  exact ⟨
    w,
    admitted,
    selected,
    ConformancePlan.groupGroupNotice_unpublished
      (inputs := [[first]])
      generated valid
      (by cbv)
      history ledger admitted streamReady
      (streamCuts := streamCuts)
      (by rw [exactCuts]; exact mergeFailureCuts_partition _ _)
      selected List.mem_cons_self
  ⟩

end GroupCarrier

namespace ItemCarrier

private def selections : List Selection :=
  [field "users" [defer [defer [field "name"] (some "C")] (some "W")] [.stream]]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 50 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def stream : DeliveryNode := { key := 0, path := [.field "users"] }

private def child : DeliveryNode :=
  { key := 2, path := [.field "users", .index 0], label := some (.string "C") }

private def children (key index : Nat) (name : String) : Execution.Work :=
  let path := [.field "users", .index index]
  let ancestor : DeliveryNode := { key := key - 1, path, label := some (.string "W") }
  let node : DeliveryNode := { key, path, label := some (.string "C") }
  .combine .empty
    (.combine
      (.executionGroup [⟨node, [ancestor]⟩] path (.ok ([("name", .scalar name)], 0))
        (.combine .empty .empty)) .empty)

private def item : StreamItem :=
  {
    occurrence := .item [0, 0, 1] 0,
    value := ⟨.object [], 0⟩,
    work := Work.fromExecution (children 2 0 "name1") [0, 0, 1, 0]
  }

private def first : GraphEvent := .streamItems stream [item]

private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0, selections, rfl⟩

private theorem valid : ValidGraphEvents work [first] := by
  have known : TaskAt work item.occurrence [stream.key] none
      (.item stream (.ok (.object [], 0))) :=
    .item (items := [(.ok (.object [], 0), children 2 0 "name1"),
      (.ok (.object [], 0), children 4 1 "name2")]) (owners := []) (by cbv) rfl
  apply ValidGraphEvents.append ValidGraphEvents.nil
  · intro current member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, _, known, by cbv⟩
  · simp [first, item, GraphEvent.Fresh, GraphEvent.identities]
  · refine ⟨[0, 0, 1], [(.ok (.object [], 0), children 2 0 "name1"),
      (.ok (.object [], 0), children 4 1 "name2")], none, [], by cbv,
      by simp, by simp, ?_, by cbv⟩
    intro source impossible; cases impossible

/-- An actual streamed-item integration has unique notices after taskless promotion.
Witness: matching item work supplies canonical parents; generic integration pruning
derives uniqueness without assuming that the original wrapper has a task of its own.
-/
theorem promoted_item_frontier_unique
    : let initial := State.initialize (Work.fromExecution work)
      let integrated := initial.maybeIntegrateWork item.work
      (((integrated.1.pruneEmptyGroups integrated.2.newGroups).2).map
        DeliveryNode.key).Nodup := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have links := createWorkQueue_childLinksCanonical (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
  have matched := valid.eachMatches List.mem_cons_self
  exact State.maybeIntegrateWork_pruned_unique links (createWorkQueue_childGroupsUnique _)
    item.work (fun _ member =>
      matched.streamItem_childGroups_parentCanonical canonical List.mem_cons_self member)

/-- A streamed object announces its real deferred child through a taskless wrapper.
Witness: exact executable item replay and generic atomized provenance. This exercises
the other notice-bearing constructor without assuming parentless post-pruning groups.
-/
theorem promoted_child_located
    : inputsStarted work [[first]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized [[first]]).2.flatten
        = [.streamValues stream [⟨item.value.item, item.value.errors⟩] [child] []]
      ∧ ∃ dependencies producer, NodeAt work child .group dependencies producer := by
  refine ⟨by cbv, by cbv, ?_⟩
  have noticed := createWorkQueue_runNormalized_atomicGroupNoticesLocated generated
    (inputs := [[first]]) valid
    (.streamValues stream [⟨item.value.item, item.value.errors⟩] [child] [])
    (by cbv; exact .head _)
  exact noticed child List.mem_cons_self

end ItemCarrier

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerGroupNotices
