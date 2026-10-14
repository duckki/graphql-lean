import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedAncestry

/-! Exact suffix reuse for ancestor construction. The executable model still uses
filtered lookup lists. These proof-side constructors reuse a parent's stored suffix
under internally maintained context coherence, without weakening the host contract. -/

namespace GraphQL.IncrementalDelivery.Semantics.SharedAncestorConstruction

open GraphQL.IncrementalDelivery.Execution
open Ancestry

def resolve (context : DeferMap) (keys : List Nat) : List DeliveryNode :=
  keys.filterMap
    (fun key => (lookupDeferredFragment? context key).map DeferredFragment.node)

/-- Runtime-refinement target: reuse a parent's full suffix without rebuilding it from
keys. A missing parent still permits older ancestors. Exactness requires context coherence
and matching parent ancestry; arbitrary helper inputs use the public filtered constructor.
-/
def sharedDeferAncestors (deferMap : DeferMap) (ancestors : List Nat)
    : List DeliveryNode :=
  match ancestors with
  | [] => []
  | parent :: rest =>
      match lookupDeferredFragment? deferMap parent with
      | some fragment => fragment.node :: fragment.ancestors
      | none =>
          rest.filterMap
            (fun key => (lookupDeferredFragment? deferMap key).map DeferredFragment.node)

/-- Proof-facing shared constructor for implementation optimization. Generated collection
allows one parent lookup and one cons instead of a full ancestor traversal. The public
executor retains `Execution.getNewDeferMap`; the theorems below and in
`SharedAncestorCollection` establish when this builder gives exactly the same ordered map.
Map lookup and append remain abstracted by lists, not optimized container implementations.
-/
def getNewDeferMapShared (usages : List DeferUsage) (path : ResponsePath)
    (deferMap : DeferMap)
    : DeferMap :=
  usages.foldl
    (fun current usage =>
      current
      ++ [{
            node := { ref := usage.ref, path, label := usage.label }
            ancestors := sharedDeferAncestors current usage.ancestors
          }])
    deferMap

/-- Stored ancestor descriptors agree with the current context's first lookup. -/
def Coherent (context : DeferMap) : Prop :=
  ∀ fragment ∈ context,
  ∀ node ∈ fragment.ancestors,
    (lookupDeferredFragment? context node.ref).map DeferredFragment.node = some node

theorem coherent_empty : Coherent [] := by
  simp [Coherent]

theorem lookup_append_of_some {context : DeferMap} {key : Nat}
    {fragment : DeferredFragment}
    (found : lookupDeferredFragment? context key = some fragment) (more : DeferMap)
    : lookupDeferredFragment? (context ++ more) key = some fragment := by
  simp only [lookupDeferredFragment?, List.find?_append] at found ⊢
  simp [found]

theorem resolve_mem {context : DeferMap} {keys : List Nat} {node : DeliveryNode}
    (member : node ∈ resolve context keys)
    : (lookupDeferredFragment? context node.ref).map DeferredFragment.node
      = some node := by
  obtain ⟨key, _, found⟩ := List.mem_filterMap.mp member
  obtain ⟨fragment, lookup, equal⟩ := Option.map_eq_some_iff.mp found
  subst node
  rw [lookup_ref lookup, lookup]
  rfl

theorem resolve_stored {context : DeferMap} (coherent : Coherent context)
    {fragment : DeferredFragment} (member : fragment ∈ context)
    : resolve context (fragment.ancestors.map DeliveryNode.ref) = fragment.ancestors := by
  have aux (nodes : List DeliveryNode)
      (known : ∀ node ∈ nodes,
        (lookupDeferredFragment? context node.ref).map DeferredFragment.node = some node)
      : resolve context (nodes.map DeliveryNode.ref) = nodes := by
    induction nodes with
    | nil => rfl
    | cons node rest ih =>
        have tail := ih (fun n hn => known n (List.mem_cons_of_mem node hn))
        simpa only [List.map_cons, resolve, List.filterMap_cons, known node (by simp),
          Option.map_some]
          using congrArg (node :: ·) tail
  exact aux fragment.ancestors (coherent fragment member)

theorem coherent_extend {context : DeferMap} (coherent : Coherent context)
    (node : DeliveryNode) (keys : List Nat)
    : Coherent (context ++ [{ node, ancestors := resolve context keys }]) := by
  intro fragment member ancestor ha
  have old : (lookupDeferredFragment? context ancestor.ref).map DeferredFragment.node
      = some ancestor := by
    rcases List.mem_append.mp member with member | member
    · exact coherent fragment member ancestor ha
    · obtain rfl := List.mem_singleton.mp member
      exact resolve_mem ha
  obtain ⟨parent, found, equal⟩ := Option.map_eq_some_iff.mp old
  rw [lookup_append_of_some found]
  exact congrArg some equal

theorem coherent_getNewDeferMap (usages : List DeferUsage) (path : ResponsePath)
    {context : DeferMap} (coherent : Coherent context)
    : Coherent (getNewDeferMap usages path context) := by
  induction usages generalizing context with
  | nil => exact coherent
  | cons usage rest ih =>
      exact ih (coherent_extend coherent
        { ref := usage.ref, path, label := usage.label } usage.ancestors)

/-- Generated children extend this full usage path, not merely a parent dependency. -/
def parentKeys (parent : Option DeferUsage) : List Nat :=
  (parent.map (fun usage => usage.ref :: usage.ancestors)).getD []

/-- One lookup and one cons on the coherent-parent path. Missing parents fall back to
the exact filtered lookup of the remaining ancestors; this does not drop older ones. -/
def fromParent (context : DeferMap) (parent : Option DeferUsage) : List DeliveryNode :=
  sharedDeferAncestors context (parentKeys parent)

/-- Parent reuse also needs the usage's exact suffix, not just matching parent keys. -/
def ParentMatches (context : DeferMap) (parent : Option DeferUsage) : Prop :=
  ∀ usage ∈ parent,
    ∀ fragment,
      lookupDeferredFragment? context usage.ref = some fragment
      → fragment.ancestors.map DeliveryNode.ref = usage.ancestors

theorem fromParent_eq {context : DeferMap} (coherent : Coherent context)
    (parent : Option DeferUsage) (matching : ParentMatches context parent)
    : fromParent context parent = resolve context (parentKeys parent) := by
  cases parent with
  | none => rfl
  | some usage =>
      cases found : lookupDeferredFragment? context usage.ref with
      | none => simp [fromParent, sharedDeferAncestors, parentKeys, resolve, found]
      | some fragment =>
          have suffix := matching usage rfl fragment found
          have same := resolve_stored coherent (List.mem_of_find?_eq_some found)
          rw [suffix] at same
          simp [fromParent, sharedDeferAncestors, parentKeys, resolve, found] at same ⊢
          exact same.symm

theorem parentMatches_of_generated {parents : Assignment} {bound : Nat}
    {context : DeferMap} {parent : Option DeferUsage}
    (metadata : MapAt parents bound context)
    (known : OptionalUsageAt parents bound context parent)
    : ParentMatches context parent := by
  intro usage member fragment found
  have exactKeys := (metadata fragment (List.mem_of_find?_eq_some found)).1.2
  rw [lookup_ref found, (known usage member).2.1] at exactKeys
  exact exactKeys

def extendFromParent (context : DeferMap) (key : Nat) (path : ResponsePath)
    (label : Option DirectiveLabel) (parent : Option DeferUsage)
    : DeferMap :=
  context
  ++ [{ node := { ref := key, path, label }, ancestors := fromParent context parent }]

/-- The construction target keeps complete node descriptors and ordered ancestry. -/
def ParentExtensionExact : Prop :=
  ∀ (parents : Assignment) bound context parent,
    Coherent context
    → MapAt parents bound context
    → OptionalUsageAt parents bound context parent
    → ∀ key path label,
        extendFromParent context key path label parent
        = getNewDeferMap [{ ref := key, label, ancestors := parentKeys parent }] path
            context

theorem parentExtensionExact_of_reuse
    (reuse
      : ∀ context,
          Coherent context
          → ∀ parent,
              ParentMatches context parent
              → fromParent context parent = resolve context (parentKeys parent))
    : ParentExtensionExact := by
  intro parents bound context parent coherent metadata known key path label
  simp only [extendFromParent, getNewDeferMap, List.foldl_cons, List.foldl_nil]
  rw [reuse context coherent parent (parentMatches_of_generated metadata known)]
  rfl

theorem parentExtensionExact_holds : ParentExtensionExact :=
  parentExtensionExact_of_reuse
    (fun _ coherent parent matching =>
      fromParent_eq coherent parent matching)

/-- Actual collection preserves the metadata needed by the shared constructor. -/
theorem collectFields_parentExtension (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (parent : Option DeferUsage) (parents : Assignment) (state : Nat)
    (context : DeferMap) (path : ResponsePath) (valid : Valid parents state)
    (metadata : MapAt parents state context)
    (known : OptionalUsageAt parents state context parent) (coherent : Coherent context)
    : let output :=
        (collectFields schema variables parentType source selections parent).run state
      let next := getNewDeferMap output.1.newDeferUsages path context
      ∀ group ∈ output.1.collectedFieldsMap,
      ∀ field ∈ group.2,
        ∀ key childPath label,
          extendFromParent next key childPath label field.deferUsage
          = getNewDeferMap
              [{ ref := key, label, ancestors := parentKeys field.deferUsage }] childPath
              next := by
  dsimp only
  obtain ⟨_, nextParents, _, _, nextMetadata, fields⟩ :=
    collectFields_ancestry schema variables parentType source selections parent
      parents state context path valid metadata known
  intro group member field hf key childPath label
  exact parentExtensionExact_holds nextParents _ _ _
    (coherent_getNewDeferMap _ _ coherent) nextMetadata (fields group member field hf)
    key childPath label

/-- Root collection discharges all context premises internally, for arbitrary selections. -/
theorem rootCollection_parentExtension (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (state : Nat) (path : ResponsePath)
    : let output :=
        (collectFields schema variables parentType source selections none).run state
      let context := getNewDeferMap output.1.newDeferUsages path []
      ∀ group ∈ output.1.collectedFieldsMap,
      ∀ field ∈ group.2,
        ∀ key childPath label,
          extendFromParent context key childPath label field.deferUsage
          = getNewDeferMap
              [{ ref := key, label, ancestors := parentKeys field.deferUsage }] childPath
              context :=
  collectFields_parentExtension schema variables parentType source selections none
    (fun _ => []) state [] path (by simp [Valid]) (by simp [MapAt])
    (by simp [OptionalUsageAt]) coherent_empty

end GraphQL.IncrementalDelivery.Semantics.SharedAncestorConstruction
