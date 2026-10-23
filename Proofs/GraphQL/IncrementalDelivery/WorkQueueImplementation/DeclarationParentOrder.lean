import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutionDeclarations

/-! GetNewDeferMap declarations retain parent-first creation order without numeric sorting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.DeclarationCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics.Ancestry
open WorkQueueSemantics (NodeRefs)

/-- Each declaration's immediate parent is known before that declaration is processed. -/
def DeclarationParentsBefore (known : NodeRefs) : List DeferredFragment → Prop
  | [] => True
  | fragment :: rest =>
      (∀ parent,
        fragment.ancestors.head?.map DeliveryNode.ref = some parent → parent ∈ known)
      ∧ DeclarationParentsBefore (known ++ [fragment.node.ref]) rest

/-- Appending usages preserves every earlier map lookup and its immutable descriptor. -/
theorem lookup_getNewDeferMap_of_some {old : DeferMap} {ref : NodeRef}
    {fragment : DeferredFragment}
    (found : lookupDeferredFragment? old ref = some fragment) (usages : List DeferUsage)
    (path : ResponsePath)
    : lookupDeferredFragment? (getNewDeferMap usages path old) ref = some fragment := by
  induction usages generalizing old with
  | nil => exact found
  | cons usage rest ih =>
      apply ih
      simp only [lookupDeferredFragment?, List.find?_append] at found ⊢
      simp only [found, Option.some_or]

/-- A fragment found after one fresh usage has its parent in the preceding map.
The new fragment resolves ancestors only against that preceding map. Existing fragments
retain the same guarantee through the independently derived map-closure invariant. -/
theorem getNewDeferMap_single_parent_known {old : DeferMap} (closed : ClosedMap old)
    (usage : DeferUsage) (path : ResponsePath) {fragment : DeferredFragment}
    (found
      : lookupDeferredFragment? (getNewDeferMap [usage] path old) usage.ref
        = some fragment)
    {parent : NodeRef}
    (parentEq : fragment.ancestors.head?.map DeliveryNode.ref = some parent)
    : parent ∈ mapRefs old := by
  have member := List.mem_of_find?_eq_some found
  change fragment ∈ old ++ [_] at member
  obtain ⟨ancestor, first, same⟩ := Option.map_eq_some_iff.mp parentEq
  have selected := List.mem_of_mem_head? first
  rcases List.mem_append.mp member with prior | fresh
  · exact same ▸ closed.ancestors fragment prior ancestor selected
  · obtain rfl := List.mem_singleton.mp fresh
    obtain ⟨ref, _, lookup⟩ := List.mem_filterMap.mp selected
    obtain ⟨previous, previousFound, identity⟩ := Option.map_eq_some_iff.mp lookup
    subst ancestor
    exact same ▸ List.mem_map.mpr ⟨previous, List.mem_of_find?_eq_some previousFound, rfl⟩

/-- Explicit plan declarations preserve parent-first order under their inherited map.
This follows actual GetNewDeferMap insertion and stable lookup. Neither sorting refs nor
repeating inherited declarations is required. It establishes the local declaration order;
execution/registration context transport remains a separate proof obligation. -/
theorem getNewDeferMap_declarations_parentsBefore (usages : List DeferUsage)
    (path : ResponsePath) (old : DeferMap) (closed : ClosedMap old)
    : DeclarationParentsBefore (mapRefs old)
        (usages.filterMap
          (fun usage =>
            lookupDeferredFragment? (getNewDeferMap usages path old) usage.ref)) := by
  induction usages generalizing old with
  | nil => trivial
  | cons usage rest ih =>
      let next := getNewDeferMap [usage] path old
      have present : usage.ref ∈ mapRefs next := by
        rw [getNewDeferMap_refs]
        exact List.mem_append_right _ List.mem_cons_self
      obtain ⟨fragment, found⟩ := lookup_exists present
      have retained := lookup_getNewDeferMap_of_some found rest path
      have expansion : getNewDeferMap (usage :: rest) path old = getNewDeferMap rest path next := rfl
      rw [expansion, List.filterMap_cons, retained]
      refine ⟨
        fun parent parentEq =>
          getNewDeferMap_single_parent_known closed usage path found parentEq,
        ?_
      ⟩
      have later := ih next (closedMap_getNewDeferMap [usage] path old closed)
      have refs : mapRefs next = mapRefs old ++ [fragment.node.ref] := by
        rw [getNewDeferMap_refs, lookup_ref found]
        rfl
      rw [refs] at later
      exact later

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.DeclarationCoverage
