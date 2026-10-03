import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildUniqueness

/-! Coverage of the executable failure-removal traversal, including stale child refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Live descendants and the finite forest used by removal
-----------------------------------------------------------------------------------------

/-- A stored group is reachable from `root` through live child links in `queue`.
This proof-only relation describes existing queue records, not a second work graph.
-/
inductive State.LiveDescendant (queue : State) : Nat → Nat → Prop
  | self {ref node} (found : queue.groupNode? ref = some node)
    : queue.LiveDescendant ref ref
  | child {ref node child target} (found : queue.groupNode? ref = some node)
    (linked : child ∈ node.childGroups) (below : queue.LiveDescendant child target)
    : queue.LiveDescendant ref target

/-- The queue's stored child lists are duplicate-free and follow one parent per ref.
Live child edges increase delivery refs; stale refs need not name live records.
These are traversal proof premises, not additional host-source or conformance laws.
-/
structure State.RemovalForest (queue : State) (parents : Nat → NodeRefs) : Prop where
  uniqueChildren : queue.ChildGroupsUnique
  canonical : queue.ChildLinksCanonical parents
  increasing
    : ∀ {parent child : GroupNode},
        parent ∈ queue.groupNodes
        → child ∈ queue.groupNodes
        → child.group.node.ref ∈ parent.childGroups
        → parent.group.node.ref < child.group.node.ref

/-- Every live-descendant path starts at an existing queue group.
Witness: either path constructor contains the initial successful lookup.
-/
theorem State.LiveDescendant.found {queue : State} {root target}
    (path : queue.LiveDescendant root target)
    : ∃ node, queue.groupNode? root = some node := by
  cases path with
  | self found => exact ⟨_, found⟩
  | child found _ _ => exact ⟨_, found⟩

/-- Generated metadata supplies the forest's parent and strict-ref properties.
Witness: a canonical live edge is the head of the child's generated ancestor list.
Duplicate-free child lists come from concrete bookkeeping preservation.
-/
theorem State.RemovalForest.of_generated
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (generated : ExecutedWork work)
    (uniqueChildren : queue.ChildGroupsUnique)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (workCanonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : queue.RemovalForest parents := by
  refine ⟨uniqueChildren, links, ?_⟩
  intro parent child parentMember childMember linked
  obtain ⟨dependencies, known⟩ := matching child childMember
  have head : dependencies.head? = some parent.group.node.ref := by
    rw [workCanonical child.group.node dependencies known]
    exact links parent parentMember child.group.node.ref linked
  cases dependencies with
  | nil => simp at head
  | cons first rest =>
      have same : first = parent.group.node.ref := Option.some.inj head
      subst first
      exact generated.groupRecordAncestorSmaller known (by simp)

-----------------------------------------------------------------------------------------
-- Each live visit spends one unit of a sufficient traversal budget
-----------------------------------------------------------------------------------------

/-- The collector frontier contains no repeated ref, and each non-root ref was
enqueued by an already visited parent. Live frontier refs lie above the starting ref.
The strict budget bounds visits by the number of live queue records, not stale links.
-/
private structure RemovalFrontier (queue : State) (parents : Nat → NodeRefs)
    (root fuel : Nat) (pending removed : NodeRefs)
    : Prop where
  rootPresent : ∃ node, queue.groupNode? root = some node
  unique : (removed ++ pending).Nodup
  present : ∀ ref ∈ removed, ∃ node, queue.groupNode? ref = some node
  introduced
    : ∀ ref ∈ removed ++ pending,
        ref = root ∨ ∃ parent ∈ removed, (parents ref).head? = some parent
  lower
    : ∀ ref ∈ removed ++ pending, (∃ node, queue.groupNode? ref = some node) → root ≤ ref
  budget : queue.groupNodes.length < fuel + removed.length

/-- A valid frontier cannot exhaust its budget while retaining its invariant.
Witness: visited refs are distinct live refs, so their count is at most the map size.
-/
private theorem RemovalFrontier.fuel_pos
    {queue : State} {parents root fuel pending removed}
    (frontier : RemovalFrontier queue parents root fuel pending removed)
    : 0 < fuel := by
  have included : removed.Subset (queue.groupNodes.map (fun node => node.group.node.ref)) := by
    intro ref member
    obtain ⟨node, found⟩ := frontier.present ref member
    exact List.mem_map.mpr
      ⟨node, List.mem_of_find?_eq_some found, State.groupNode?_ref found⟩
  have bound := (List.nodup_append.mp frontier.unique).1.length_le_of_subset included
  simp only [List.length_map] at bound
  have budget := frontier.budget
  omega

/-- Skipping a missing ref preserves all live-visit accounting.
Witness: restrict the frontier; neither visited refs nor the budget changes.
-/
private theorem RemovalFrontier.skip
    {queue : State} {parents root fuel head rest removed}
    (frontier : RemovalFrontier queue parents root fuel (head :: rest) removed)
    : RemovalFrontier queue parents root fuel rest removed := by
  have subset : (removed ++ rest).Subset (removed ++ head :: rest) := by
    intro ref member
    simp only [List.mem_append, List.mem_cons] at member ⊢
    exact member.imp_right Or.inr
  exact {
    rootPresent := frontier.rootPresent
    unique := frontier.unique.sublist (by simp)
    present := frontier.present
    introduced := fun ref member => frontier.introduced ref (subset member)
    lower := fun ref member => frontier.lower ref (subset member)
    budget := frontier.budget
  }

/-- Visiting a live ref cannot re-enqueue a visited or pending ref.
Witness: each child has this unique parent, which is not yet visited; a live edge
back to the traversal root is excluded by strict ref increase.
-/
private theorem RemovalFrontier.visit
    {queue : State} {parents root fuel head rest removed node}
    (forest : queue.RemovalForest parents)
    (frontier : RemovalFrontier queue parents root (fuel + 1) (head :: rest) removed)
    (found : queue.groupNode? head = some node)
    : RemovalFrontier queue parents root fuel (node.childGroups ++ rest)
        (head :: removed) := by
  have nodeMember : node ∈ queue.groupNodes := List.mem_of_find?_eq_some found
  have nodeRef := State.groupNode?_ref found
  obtain ⟨removedUnique, pendingUnique, separate⟩ := List.nodup_append.mp frontier.unique
  have headAbsent : head ∉ removed := by
    intro member
    exact separate head member head (by simp) rfl
  have restAbsent := (List.nodup_cons.mp pendingUnique).1
  have headLower := frontier.lower head (by simp) ⟨node, found⟩
  have childParent {child} (member : child ∈ node.childGroups)
      : (parents child).head? = some head := by
    simpa only [nodeRef] using forest.canonical node nodeMember child member
  have fresh {child} (member : child ∈ node.childGroups)
      : child ∉ removed ++ head :: rest := by
    intro old
    rcases frontier.introduced child old with same | ⟨parent, visited, parentEq⟩
    · have live : ∃ childNode, queue.groupNode? child = some childNode :=
        same ▸ frontier.rootPresent
      obtain ⟨childNode, childFound⟩ := live
      have greater := forest.increasing nodeMember (List.mem_of_find?_eq_some childFound)
        (State.groupNode?_ref childFound ▸ member)
      rw [nodeRef, State.groupNode?_ref childFound, same] at greater
      simp only [NodeRef] at *
      omega
    · have sameParent : parent = head := Option.some.inj (parentEq.symm.trans (childParent member))
      exact headAbsent (sameParent ▸ visited)
  refine {
    rootPresent := frontier.rootPresent
    unique := ?_
    present := ?_
    introduced := ?_
    lower := ?_
    budget := ?_
  }
  · simp only [List.cons_append, List.nodup_cons, List.nodup_append]
    refine ⟨?_, removedUnique, ?_, ?_⟩
    · simp only [List.mem_append, not_or]
      exact ⟨headAbsent, fun child => fresh child (by simp), restAbsent⟩
    · refine ⟨forest.uniqueChildren node nodeMember, (List.nodup_cons.mp pendingUnique).2, ?_⟩
      intro child member ref tail same
      subst ref
      exact fresh member (by simp [tail])
    · intro ref member child next same
      subst child
      rcases List.mem_append.mp next with child | tail
      · exact fresh child (by simp [member])
      · exact separate ref member ref (by simp [tail]) rfl
  · intro ref member
    rcases List.mem_cons.mp member with same | earlier
    · exact same ▸ ⟨node, found⟩
    · exact frontier.present ref earlier
  · intro ref member
    simp only [List.cons_append, List.mem_cons, List.mem_append] at member
    rcases member with same | earlier | child | tail
    · subst ref
      exact (frontier.introduced head (by simp)).imp_right
        (fun ⟨parent, member, eq⟩ => ⟨parent, by simp [member], eq⟩)
    · exact (frontier.introduced ref (by simp [earlier])).imp_right
        (fun ⟨parent, member, eq⟩ => ⟨parent, by simp [member], eq⟩)
    · exact Or.inr ⟨head, by simp, childParent child⟩
    · exact (frontier.introduced ref (by simp [tail])).imp_right
        (fun ⟨parent, member, eq⟩ => ⟨parent, by simp [member], eq⟩)
  · intro ref member live
    simp only [List.cons_append, List.mem_cons, List.mem_append] at member
    rcases member with same | earlier | child | tail
    · simpa only [same] using headLower
    · exact frontier.lower ref (by simp [earlier]) live
    · obtain ⟨childNode, childFound⟩ := live
      have greater := forest.increasing nodeMember (List.mem_of_find?_eq_some childFound)
        (State.groupNode?_ref childFound ▸ child)
      rw [nodeRef, State.groupNode?_ref childFound] at greater
      simp only [NodeRef] at *
      omega
    · exact frontier.lower ref (by simp [tail]) live
  · have budget := frontier.budget
    simp only [List.length_cons]
    omega

/-- The collector visits every live descendant of its current frontier.
Witness: induction on live fuel and the pending list; stale refs consume only the
list induction, and distinct live visits cannot exhaust the strictly sufficient budget.
-/
private theorem RemovalFrontier.collect_covers
    {queue : State} {parents root}
    (forest : queue.RemovalForest parents) (fuel : Nat) (pending removed : NodeRefs)
    (frontier : RemovalFrontier queue parents root fuel pending removed)
    : removed.Subset (State.removeGroup.collect fuel queue pending removed)
      ∧ ∀ ref ∈ pending,
          ∀ target,
            queue.LiveDescendant ref target
            → target ∈ State.removeGroup.collect fuel queue pending removed := by
  induction fuel generalizing pending removed with
  | zero => exact False.elim (by have positive := frontier.fuel_pos; omega)
  | succ fuel ih =>
      induction pending generalizing removed with
      | nil =>
          simp only [State.removeGroup.collect, List.not_mem_nil, false_implies,
            implies_true, and_true]
          exact List.Subset.refl _
      | cons head rest tailIH =>
          cases found : queue.groupNode? head with
          | none =>
              have next := tailIH removed frontier.skip
              simp only [State.removeGroup.collect, found]
              refine ⟨next.1, ?_⟩
              intro ref member target path
              rcases List.mem_cons.mp member with same | later
              · subst ref
                obtain ⟨node, present⟩ := path.found
                simp [found] at present
              · exact next.2 ref later target path
          | some node =>
              have next := ih (node.childGroups ++ rest) (head :: removed)
                (frontier.visit forest found)
              simp only [State.removeGroup.collect, found]
              refine ⟨fun _ member => next.1 (by simp [member]), ?_⟩
              intro ref member target path
              rcases List.mem_cons.mp member with same | later
              · subst ref
                cases path with
                | self present => exact next.1 (by simp)
                | child present linked below =>
                    have same := Option.some.inj (found.symm.trans present)
                    subst node
                    exact next.2 _ (List.mem_append_left _ linked) target below
              · exact next.2 ref (List.mem_append_right _ later) target path

-----------------------------------------------------------------------------------------
-- The implementation's actual budget removes every live descendant
-----------------------------------------------------------------------------------------

/-- Every collected ref was already removed or is reached through a pending live root.
Witness: induction on the executable collector, prefixing a real child edge when the
recursive call expands a found group. This direction needs no forest invariant.
-/
theorem State.removeGroup_collect_provenance
    (fuel : Nat) (queue : State) (pending removed : NodeRefs) {target}
    (member : target ∈ State.removeGroup.collect fuel queue pending removed)
    : target ∈ removed ∨ ∃ root ∈ pending, queue.LiveDescendant root target := by
  induction fuel generalizing pending removed with
  | zero => exact Or.inl (by simpa only [State.removeGroup.collect] using member)
  | succ fuel ih =>
      induction pending generalizing removed with
      | nil => exact Or.inl (by simpa only [State.removeGroup.collect] using member)
      | cons head rest tailIH =>
          cases found : queue.groupNode? head with
          | none =>
              rw [State.removeGroup.collect, found] at member
              rcases tailIH removed member with earlier | ⟨root, inRest, path⟩
              · exact Or.inl earlier
              · exact Or.inr ⟨root, by simp [inRest], path⟩
          | some node =>
              rw [State.removeGroup.collect, found] at member
              rcases ih (node.childGroups ++ rest) (head :: removed) member with
                earlier | ⟨root, inPending, path⟩
              · rcases List.mem_cons.mp earlier with same | earlier
                · subst target
                  exact Or.inr ⟨head, by simp, .self found⟩
                · exact Or.inl earlier
              · rcases List.mem_append.mp inPending with child | later
                · exact Or.inr ⟨head, by simp, .child found child path⟩
                · exact Or.inr ⟨root, by simp [later], path⟩

/-- The implementation's node-count budget covers every stored live descendant.
Witness: initialize the finite-frontier invariant at the requested root; no bound
on the number or placement of missing child refs is needed.
-/
theorem State.removeGroup_collect_covers
    {queue : State} {parents root target}
    (forest : queue.RemovalForest parents)
    (path : queue.LiveDescendant root target)
    : target
      ∈ State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] [] := by
  have frontier : RemovalFrontier queue parents root (queue.groupNodes.length + 1)
      [root] [] := {
    rootPresent := path.found
    unique := by simp
    present := by simp
    introduced := by intro ref member; exact Or.inl (by simpa using member)
    lower := by intro ref member _; simp_all
    budget := by simp
  }
  exact (frontier.collect_covers forest _ _ _).2 root (by simp) target path

/-- The actual removal ref set is exactly the stored live-descendant set.
Witness: collector provenance gives soundness and the live-node budget gives coverage.
Unrelated groups and missing child refs are never included in the removal set.
-/
theorem State.removeGroup_collect_mem_iff
    {queue : State} {parents root target}
    (forest : queue.RemovalForest parents)
    : target ∈ State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] []
      ↔ queue.LiveDescendant root target := by
  constructor
  · intro member
    rcases State.removeGroup_collect_provenance _ _ _ _ member with
      impossible | ⟨ref, member, path⟩
    · cases impossible
    · exact List.mem_singleton.mp member ▸ path
  · exact State.removeGroup_collect_covers forest

/-- A live descendant cannot survive group removal as a stored node or active root.
Witness: coverage by the real collector and the handler's two ref filters.
-/
theorem State.removeGroup_liveDescendant_absent
    {queue : State} {parents root target}
    (forest : queue.RemovalForest parents)
    (path : queue.LiveDescendant root target)
    : (queue.removeGroup root).groupNode? target = none
      ∧ target ∉ (queue.removeGroup root).rootGroups := by
  have removed := State.removeGroup_collect_covers forest path
  let refs := State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] []
  have member : target ∈ refs := removed
  constructor
  · change (queue.groupNodes.filter
      (fun node => !refs.contains node.group.node.ref)).find?
        (fun node => node.group.node.ref == target) = none
    apply List.find?_eq_none.mpr
    intro node kept
    have absent := (List.mem_filter.mp kept).2
    by_cases same : node.group.node.ref = target
    · simp [same, member] at absent
    · simpa using same
  · change target ∉ queue.rootGroups.filter (fun ref => !refs.contains ref)
    simp [member]

-----------------------------------------------------------------------------------------
-- Generated replay discharges every structural traversal premise
-----------------------------------------------------------------------------------------

/-- Every matched generated replay has a finite removal forest.
Witness: unconditional child-list uniqueness, generated primary-parent coherence,
and strict ancestor-ref order. Neither start discipline nor output conformance is assumed.
-/
theorem ExecutedWork.runNormalized_removalForest
    {work : Execution.Work} (generated : ExecutedWork work)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    : ∃ parents,
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.RemovalForest
          parents := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have matched : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work := by
    intro batch batchMember event member
    exact valid.eachMatches (List.mem_flatten.mpr ⟨batch, batchMember, member⟩)
  have initial := createWorkQueue_childLinksCanonical (Work.fromExecution work) parents (by
    intro group member
    exact workFromSpec_groups_parentCanonical (Located.root (root := work))
      canonical member)
  exact ⟨parents, State.RemovalForest.of_generated generated
    (createWorkQueue_runNormalized_childGroupsUnique (Work.fromExecution work) batches)
    (initial.runNormalized batches matched canonical)
    ((createWorkQueue_groupNodesMatchWork work).runNormalized batches matched) canonical⟩

/-- Failure removal covers every live descendant after any matched generated replay.
Witness: derive the traversal forest from execution and queue transitions, then apply
coverage for the implementation's actual finite budget. No forest premise is exported.
-/
theorem ExecutedWork.runNormalized_removeGroup_covers
    {work : Execution.Work} (generated : ExecutedWork work)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    {root target}
    (path
      : ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.LiveDescendant
          root target)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      (queue.removeGroup root).groupNode? target = none
      ∧ target ∉ (queue.removeGroup root).rootGroups := by
  obtain ⟨parents, forest⟩ := generated.runNormalized_removalForest batches valid
  exact State.removeGroup_liveDescendant_absent forest path

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
