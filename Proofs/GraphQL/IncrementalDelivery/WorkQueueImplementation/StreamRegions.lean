import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedRefRegions

/-! Stream-item identities index the executor's already-separated ref regions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open Semantics.RefRegions

-----------------------------------------------------------------------------------------
-- Label the existing hidden regions by their producing stream-item occurrence
-----------------------------------------------------------------------------------------

/-- Hidden ref regions paired with the stream-item occurrence that reveals them.
The address is the current subtree's absolute structural address in the original work. -/
def streamRegions (work : Execution.Work) (address : Address := [])
    : List (Occurrence × NodeRefs) :=
  match work with
  | .empty => []
  | .combine left right =>
      streamRegions left (address ++ [0]) ++ streamRegions right (address ++ [1])
  | .executionGroup _ _ _ children => streamRegions children (address ++ [0])
  | .stream _ items =>
      items.zipIdx.attach.flatMap
        fun pair =>
          (.item address pair.val.2, rootRefs pair.val.1.2)
          :: streamRegions pair.val.1.2 (address ++ [pair.val.2])
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have entryMember := List.fst_mem_of_mem_zipIdx pair.property
  have smaller := List.sizeOf_lt_of_mem entryMember
  rcases pair with ⟨⟨⟨result, children⟩, index⟩, member⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only at *
  omega

/-- Stream enumeration retains only ordinary occurrence labels, not membership proofs.
Witness: erase the temporary list membership evidence used for structural termination. -/
theorem streamRegions_stream (node : Execution.DeliveryNode)
    (items : List (Execution.Result Execution.ResponseValue × Execution.Work))
    (address : Address)
    : streamRegions (.stream node items) address
      = items.zipIdx.flatMap
          fun pair =>
            (.item address pair.2, rootRefs pair.1.2)
            :: streamRegions pair.1.2 (address ++ [pair.2]) := by
  rw [streamRegions, List.flatMap_subtype
    (g := fun pair => (.item address pair.2, rootRefs pair.1.2)
      :: streamRegions pair.1.2 (address ++ [pair.2])) (fun _ _ => rfl)]
  simp

/-- Erasing occurrence labels recovers exactly the original hidden-region list.
Witness: structural recursion; enumeration adds indices without changing item order. -/
theorem streamRegions_refs (work : Execution.Work) (address : Address)
    : (streamRegions work address).map Prod.snd = hiddenRegions work := by
  cases work with
  | empty => simp [streamRegions, hiddenRegions]
  | combine left right =>
      simp only [streamRegions, List.map_append, hiddenRegions]
      rw [streamRegions_refs left, streamRegions_refs right]
  | executionGroup groups path result children =>
      simpa only [streamRegions, hiddenRegions]
        using streamRegions_refs children (address ++ [0])
  | stream node items =>
      simp only [streamRegions_stream, List.map_flatMap, List.map_cons]
      have erased : ∀ pair ∈ items.zipIdx,
          rootRefs pair.1.2 :: (streamRegions pair.1.2 (address ++ [pair.2])).map Prod.snd
            = rootRefs pair.1.2 :: hiddenRegions pair.1.2 := by
        intro pair member
        rw [streamRegions_refs pair.1.2]
      rw [List.flatMap_def, List.map_congr_left erased, ← List.flatMap_def]
      rw [hiddenRegions]
      change items.zipIdx.flatMap (fun pair => regions pair.1.2) =
        items.flatMap (fun entry => regions entry.2)
      rw [← List.flatMap_map Prod.fst (fun entry => regions entry.2) items.zipIdx,
        List.zipIdx_map_fst]
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial

  all_goals
    have smaller := List.sizeOf_lt_of_mem (List.fst_mem_of_mem_zipIdx member)
    rcases pair with ⟨⟨result, children⟩, index⟩
    simp only [Prod.mk.sizeOf_spec] at smaller
    dsimp only at *
    omega

/-- Any located subtree retains its labelled hidden regions in the original work.
Witness: induction on structural navigation, including entry lookup beneath streams. -/
theorem Located.streamRegions_subset {root address current producer owners}
    (located : Located root address current producer owners)
    : (streamRegions current address).Subset (streamRegions root []) := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact List.Subset.refl _
  | left _ ih =>
      rw [streamRegions] at ih
      exact (List.subset_append_left _ _).trans ih
  | right _ ih =>
      rw [streamRegions] at ih
      exact (List.subset_append_right _ _).trans ih
  | executionGroup _ ih => simpa only [streamRegions] using ih
  | @item address node items producer owners index result children prior entry ih =>
      intro region member
      apply ih
      rw [streamRegions_stream]
      exact List.mem_flatMap.mpr ⟨((result, children), index),
        List.mk_mem_zipIdx_iff_getElem?.mpr entry, List.mem_cons_of_mem _ member⟩

/-- A stream-item lookup identifies its exact labelled root-ref region.
Witness: the located stream's enumeration and the structural inclusion theorem. -/
theorem Located.streamRegion_member
    {root address node items producer owners index result children}
    (located : Located root address (.stream node items) producer owners)
    (entry : items[index]? = some (result, children))
    : (.item address index, rootRefs children) ∈ streamRegions root [] := by
  apply Located.streamRegions_subset located
  rw [streamRegions_stream]
  exact List.mem_flatMap.mpr ⟨((result, children), index),
    List.mk_mem_zipIdx_iff_getElem?.mpr entry, List.mem_cons_self⟩

-----------------------------------------------------------------------------------------
-- Generated separation excludes refs of every still-hidden item
-----------------------------------------------------------------------------------------

/-- Pure execution already separates the root region from all stream-item regions.
Witness: instantiate the existing execution-region theorem at the generating query. -/
theorem ExecutedWork.regionsSeparated {work : Execution.Work}
    (generated : ExecutedWork work)
    : WorkSeparated work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, same⟩ := generated
  exact same ▸ executeRoot_separated schema resolvers variables fuel parentType source
    selections 0

/-- A labelled stream-item region is disjoint from the original root region.
Witness: erase its label and apply the head clause of execution-region separation. -/
theorem streamRegion_disjoint_root {work : Execution.Work}
    (separated : WorkSeparated work) {occurrence refs}
    (member : (occurrence, refs) ∈ streamRegions work [])
    : Disjoint (rootRefs work) refs := by
  apply ((separated_iff work).mp separated).1 refs
  rw [← streamRegions_refs work []]
  exact List.mem_map_of_mem member

/-- Distinct stream-item occurrences have disjoint ref regions, including nested items.
Witness: pairwise separation of the labelled list; two entries sharing a ref must be
the very same entry. Empty regions require no identity-uniqueness assumption. -/
theorem streamRegions_disjoint {work : Execution.Work} (separated : WorkSeparated work)
    {first second left right}
    (leftMember : (first, left) ∈ streamRegions work [])
    (rightMember : (second, right) ∈ streamRegions work []) (different : first ≠ second)
    : Disjoint left right := by
  have pairwise : (streamRegions work []).Pairwise (fun left right => Disjoint left.2 right.2) := by
    rw [← List.pairwise_map, streamRegions_refs]
    exact ((separated_iff work).mp separated).2
  have distinct (regions : List (Occurrence × NodeRefs))
      (separate : regions.Pairwise (fun left right => Disjoint left.2 right.2))
      (firstMember : (first, left) ∈ regions) (secondMember : (second, right) ∈ regions)
      : Disjoint left right := by
    induction regions with
    | nil => cases firstMember
    | cons head tail ih =>
        obtain ⟨headDisjoint, tailDisjoint⟩ := List.pairwise_cons.mp separate
        rcases List.mem_cons.mp firstMember with same | firstTail
        · subst head
          rcases List.mem_cons.mp secondMember with same | secondTail
          · exact False.elim (different (congrArg Prod.fst same).symm)
          · exact headDisjoint _ secondTail
        · rcases List.mem_cons.mp secondMember with same | secondTail
          · subst head
            exact (headDisjoint _ firstTail).symm
          · exact ih tailDisjoint firstTail secondTail
  exact distinct _ pairwise leftMember rightMember

-----------------------------------------------------------------------------------------
-- Only observed stream items expose a new ref region
-----------------------------------------------------------------------------------------

/-- A ref is exposed by the root work or by one of the recorded stream-item occurrences.
Recording execution-group occurrences does not expose an additional region. -/
def ExposedRef (work : Execution.Work) (seen : List Occurrence) (ref : NodeRef) : Prop :=
  ref ∈ rootRefs work
  ∨ ∃ occurrence ∈ seen, ∃ refs, (occurrence, refs) ∈ streamRegions work [] ∧ ref ∈ refs

/-- Recording more occurrences preserves every exposed ref.
Witness: retain the root case or the same recorded region witness. -/
theorem ExposedRef.mono {work before after ref} (exposed : ExposedRef work before ref)
    (included : before.Subset after)
    : ExposedRef work after ref := by
  rcases exposed with root | ⟨occurrence, member, refs, region, contains⟩
  · exact .inl root
  · exact .inr ⟨occurrence, included member, refs, region, contains⟩

/-- No ref in an unobserved stream-item region has already been exposed.
Witness: root/item separation and disjointness from every previously recorded item.
This also distinguishes different items of the same stream and nested streams. -/
theorem streamRegion_unexposed {work : Execution.Work} (separated : WorkSeparated work)
    {seen occurrence refs ref} (region : (occurrence, refs) ∈ streamRegions work [])
    (fresh : occurrence ∉ seen) (member : ref ∈ refs)
    : ¬ExposedRef work seen ref := by
  rintro (root | ⟨earlier, recorded, earlierRefs, prior, contains⟩)
  · exact streamRegion_disjoint_root separated region ref root member
  · exact streamRegions_disjoint separated prior region
      (fun same => fresh (same ▸ recorded)) ref contains member

/-- Every immediate registration ref belongs to the current root-ref region.
Witness: the region includes contributors and full ancestors; lowering selects a suffix.
-/
theorem workFromSpec_group_rootRef (work : Execution.Work) (address : Address)
    {group : Group} (member : group ∈ (Work.fromExecution work address).groups)
    : group.node.ref ∈ rootRefs work := by
  cases work with
  | empty => cases member
  | combine left right =>
      rcases List.mem_append.mp member with leftMember | rightMember
      · exact List.mem_append_left _ (workFromSpec_group_rootRef left _ leftMember)
      · exact List.mem_append_right _ (workFromSpec_group_rootRef right _ rightMember)
  | executionGroup groups path result children =>
      obtain ⟨fragment, fragmentMember, inChain⟩ := List.mem_flatMap.mp member
      obtain ⟨ancestors, suffix, _⟩ := workFromSpec_groupChain_member inChain
      exact List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨fragment, fragmentMember, List.mem_map.mpr
          ⟨group.node, suffix.sublist.subset List.mem_cons_self, rfl⟩⟩)
  | stream => cases member
termination_by sizeOf work

/-- All refs in a registered task's own defer region have been exposed.
The lookup keeps the property independent of task outcomes or queue data values. -/
def TaskRegionCovered (work : Execution.Work) (seen : List Occurrence) (task : Task)
    : Prop :=
  ∀ address location,
    task.occurrence = .executionGroup address
    → locateWork work address = some location
    → ∀ ref ∈ rootRefs location.current, ExposedRef work seen ref

/-- A task's region certificate persists as more stream items are recorded.
Witness: monotonicity of exposed refs at each located ref. -/
theorem TaskRegionCovered.mono {work before after task}
    (covered : TaskRegionCovered work before task) (included : before.Subset after)
    : TaskRegionCovered work after task := by
  intro address location same found ref member
  exact (covered address location same found ref member).mono included

/-- Lowering a covered subtree yields covered immediate task regions.
Witness: combines narrow the current region; each group task identifies its own location.
No future item region is exposed by descending through an execution-group child. -/
theorem workFromSpec_tasks_regionCovered {root current address producer owners seen}
    (located : Located root address current producer owners)
    (covered : ∀ ref ∈ rootRefs current, ExposedRef root seen ref)
    : ∀ task ∈ (Work.fromExecution current address).tasks,
        TaskRegionCovered root seen task := by
  cases current with
  | empty => intro task member; cases member
  | combine left right =>
      intro task member
      rcases List.mem_append.mp member with leftMember | rightMember
      · exact workFromSpec_tasks_regionCovered (Located.left located)
          (fun ref member => covered ref (List.mem_append_left _ member)) task leftMember
      · exact workFromSpec_tasks_regionCovered (Located.right located)
          (fun ref member => covered ref (List.mem_append_right _ member)) task rightMember
  | executionGroup groups path result children =>
      intro task member query location same found
      have taskEq := List.mem_singleton.mp member
      subst task
      have addressEq : address = query := Occurrence.executionGroup.inj same
      subst query
      have locationEq := Option.some.inj (located.symm.trans found)
      subst location
      exact covered
  | stream => intro task member; cases member
termination_by sizeOf current

/-- A matching stream item reveals exactly one located root-ref region.
Witness: source matching identifies the original item child work and its lowering. -/
theorem GraphEvent.MatchesWork.streamItem_region {work stream items}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : ∃ children address producer owners,
        Located work address children producer owners
        ∧ item.work = Work.fromExecution children address
        ∧ (item.occurrence, rootRefs children) ∈ streamRegions work [] := by
  obtain ⟨_, producer, known, childrenWork⟩ := matching item member
  cases occurrence : item.occurrence with
  | executionGroup => simp [streamItemWork?, occurrence] at childrenWork
  | item address index =>
      rw [occurrence] at known
      obtain ⟨node, entries, enclosing, result, children, located, entry, _, _⟩ := known
      change locateWork work address = some ⟨.stream node entries, producer, enclosing⟩
        at located
      have lowering : item.work = Work.fromExecution children (address ++ [index]) := by
        simpa [streamItemWork?, occurrence, located, entry] using childrenWork.symm
      exact ⟨children, address ++ [index], some (.item address index), [],
        Located.item located entry, lowering,
        occurrence ▸ Located.streamRegion_member located entry⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
