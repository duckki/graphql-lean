import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskAttachmentPaths
import Proofs.GraphQL.IncrementalDelivery.Semantics.OwnerMetadata

/-! Generated defer ancestry and stream boundaries preserve notification scopes. -/

namespace GraphQL.IncrementalDelivery.Correctness.ScopeMetadata
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics WorkQueueSemantics
open OwnerPaths

/-- A fragment's ancestor notice scopes cover its own notice scope. -/
def FragmentScoped (fragment : DeferredFragment) : Prop :=
  ∀ ancestor ∈ fragment.ancestors, ancestor.path.IsPrefix fragment.node.path

/-- Every map entry retains scope-covering defer ancestors. -/
def MapScoped (deferMap : DeferMap) : Prop :=
  ∀ fragment ∈ deferMap, FragmentScoped fragment

/-- Every node scope in the map covers the current execution attachment. -/
def MapBelow (path : ResponsePath) (deferMap : DeferMap) : Prop :=
  ∀ node ∈ mapNodes deferMap, node.path.IsPrefix path

/-- Every node scope in the map lies below the enclosing `base` scope. -/
def MapUnder (base : ResponsePath) (deferMap : DeferMap) : Prop :=
  ∀ node ∈ mapNodes deferMap, base.IsPrefix node.path

/-- Map ancestry is scope-coherent and its scopes lie between base and attachment. -/
def MapAt (base path : ResponsePath) (deferMap : DeferMap) : Prop :=
  MapScoped deferMap ∧ MapBelow path deferMap ∧ MapUnder base deferMap

mutual
  /-- Defer ancestors cover their groups; item children allocate scopes below the stream.
  This does not require a producer's task attachment to cover a reused group scope.
  -/
  def WorkScoped : Work → Prop
    | .empty => True
    | .combine left right => WorkScoped left ∧ WorkScoped right
    | .executionGroup groups _ _ children => MapScoped groups ∧ WorkScoped children
    | .stream node items => ItemsScoped node.path items

  /-- Both defer and stream notice scopes in work lie below the enclosing base scope. -/
  def ScopesUnder (base : ResponsePath) : Work → Prop
    | .empty => True
    | .combine left right => ScopesUnder base left ∧ ScopesUnder base right
    | .executionGroup groups _ _ children =>
        MapUnder base groups ∧ ScopesUnder base children
    | .stream node items => base.IsPrefix node.path ∧ ItemsUnder base items

  /-- Item child work has coherent scopes, all below the stream's list attachment. -/
  def ItemsScoped (base : ResponsePath) : List (TaskOutcome ResponseValue × Work) → Prop
    | [] => True
    | (_, children) :: rest =>
        (WorkScoped children ∧ ScopesUnder base children) ∧ ItemsScoped base rest

  /-- All item child scopes lie below base, independently of their internal coherence. -/
  def ItemsUnder (base : ResponsePath) : List (TaskOutcome ResponseValue × Work) → Prop
    | [] => True
    | (_, children) :: rest => ScopesUnder base children ∧ ItemsUnder base rest
end

/-- A completion's retained work has coherent scopes below base. -/
def Under (base : ResponsePath) (completed : Completion α) : Prop :=
  WorkScoped completed.work ∧ ScopesUnder base completed.work

-----------------------------------------------------------------------------------------
-- Map construction and completion algebra
-----------------------------------------------------------------------------------------

/-- A lookup's node occurs in the map's full metadata inventory.
Witness: the found fragment and its own node entry.
-/
theorem lookup_node_mem {deferMap ref fragment}
    (found : lookupDeferredFragment? deferMap ref = some fragment)
    : fragment.node ∈ mapNodes deferMap :=
  List.mem_flatMap.mpr
    ⟨fragment, List.mem_of_find?_eq_some found, by simp [fragmentNodes]⟩

/-- Appending a fresh fragment preserves the map's scope certificate.
Witness: its ancestors are looked-up old nodes and its own scope is the attachment.
-/
theorem MapAt.add {base path deferMap} (certified : MapAt base path deferMap)
    (below : base.IsPrefix path) (usage : DeferUsage)
    : MapAt base path
        (deferMap
          ++ [{
                node := { ref := usage.ref, path, label := usage.label }
                ancestors :=
                  usage.ancestors.filterMap
                    (fun ref =>
                      (lookupDeferredFragment? deferMap ref).map DeferredFragment.node)
              }]) := by
  let fragment : DeferredFragment :=
    { node := { ref := usage.ref, path, label := usage.label }
      ancestors := usage.ancestors.filterMap
        (fun ref => (lookupDeferredFragment? deferMap ref).map DeferredFragment.node) }
  have oldAncestor : ∀ node ∈ fragment.ancestors, node ∈ mapNodes deferMap := by
    intro node member
    obtain ⟨ref, _, mapped⟩ := List.mem_filterMap.mp member
    obtain ⟨old, found, rfl⟩ := Option.map_eq_some_iff.mp mapped
    exact lookup_node_mem found
  have nodes : ∀ node ∈ fragmentNodes fragment,
      node = fragment.node ∨ node ∈ mapNodes deferMap := by
    intro node member
    rcases List.mem_cons.mp member with own | ancestor
    · exact Or.inl own
    · exact Or.inr (oldAncestor _ ancestor)
  refine ⟨?_, ?_, ?_⟩
  · intro actual member
    rcases List.mem_append.mp member with old | fresh
    · exact certified.1 _ old
    · obtain rfl := List.mem_singleton.mp fresh
      exact fun node member => certified.2.1 _ (oldAncestor _ member)
  · intro node member
    rcases List.mem_flatMap.mp member with ⟨actual, member, inNodes⟩
    rcases List.mem_append.mp member with old | fresh
    · exact certified.2.1 _ (List.mem_flatMap.mpr ⟨actual, old, inNodes⟩)
    · obtain rfl := List.mem_singleton.mp fresh
      rcases nodes _ inNodes with own | old
      · subst node
        exact ⟨[], by simp [fragment]⟩
      · exact certified.2.1 _ old
  · intro node member
    rcases List.mem_flatMap.mp member with ⟨actual, member, inNodes⟩
    rcases List.mem_append.mp member with old | fresh
    · exact certified.2.2 _ (List.mem_flatMap.mpr ⟨actual, old, inNodes⟩)
    · obtain rfl := List.mem_singleton.mp fresh
      rcases nodes _ inNodes with own | old
      · subst node
        exact below
      · exact certified.2.2 _ old

/-- Fresh defer-map construction preserves coherent scopes between base and attachment.
Witness: fold induction through the new usages; each allocation uses the current path.
-/
theorem MapAt.new {base path deferMap} (certified : MapAt base path deferMap)
    (below : base.IsPrefix path) (usages : List DeferUsage)
    : MapAt base path (getNewDeferMap usages path deferMap) := by
  unfold getNewDeferMap
  induction usages generalizing deferMap with
  | nil => exact certified
  | cons usage rest ih =>
      rw [List.foldl_cons]
      exact ih (certified.add below usage)

/-- Descending to a child attachment preserves the inherited map's scope certificate.
Witness: transitivity of its upper path bound; lower scopes and ancestry are unchanged.
-/
theorem MapAt.below {base path next deferMap} (certified : MapAt base path deferMap)
    (below : path.IsPrefix next)
    : MapAt base next deferMap :=
  ⟨certified.1, fun node member => (certified.2.1 node member).trans below, certified.2.2⟩

/-- A partition retains a subset of the certified defer-map fragments.
Witness: every filtered lookup returns an old map entry.
-/
theorem MapScoped.filterMap {deferMap} (certified : MapScoped deferMap) (refs : NodeRefs)
    : MapScoped (refs.filterMap (lookupDeferredFragment? deferMap)) := by
  intro fragment member
  obtain ⟨ref, _, found⟩ := List.mem_filterMap.mp member
  exact certified _ (List.mem_of_find?_eq_some found)

/-- Filtered map entries retain the lower scope bound.
Witness: their fragment-node inventory is contained in the original map's inventory.
-/
theorem MapUnder.filterMap {base deferMap} (under : MapUnder base deferMap)
    (refs : NodeRefs)
    : MapUnder base (refs.filterMap (lookupDeferredFragment? deferMap)) := by
  intro node member
  obtain ⟨fragment, member, nodeMember⟩ := List.mem_flatMap.mp member
  obtain ⟨ref, _, found⟩ := List.mem_filterMap.mp member
  exact under _ (List.mem_flatMap.mpr
    ⟨fragment, List.mem_of_find?_eq_some found, nodeMember⟩)

mutual
  /-- Scope bounds may move upward without changing internal coherence.
  Witness: recursive prefix transitivity through every node inventory.
  -/
  theorem ScopesUnder.mono {base next work} (under : ScopesUnder next work)
      (below : base.IsPrefix next)
      : ScopesUnder base work := by
    cases work with
    | empty => trivial
    | combine left right => exact ⟨under.1.mono below, under.2.mono below⟩
    | executionGroup groups path result children =>
        exact ⟨fun node member => below.trans (under.1 node member), under.2.mono below⟩
    | stream node items => exact ⟨below.trans under.1, under.2.mono below⟩
  termination_by sizeOf work

  /-- Moving the item-list scope bound upward preserves every child scope.
  Witness: item-list induction and the mutually proved work-scope weakening.
  -/
  theorem ItemsUnder.mono {base next items} (under : ItemsUnder next items)
      (below : base.IsPrefix next)
      : ItemsUnder base items := by
    cases items with
    | nil => trivial
    | cons entry rest =>
        cases he : entry with
        | mk result children =>
            have small : sizeOf children ≤ sizeOf entry := by rw [he]; simp
            have child : ScopesUnder next children := by simpa only [he] using under.1
            exact ⟨child.mono below, under.2.mono below⟩
  termination_by sizeOf items
  decreasing_by all_goals subst_vars; simp_wf; omega
end

/-- A completion's lower scope bound can move upward. Witness: retained-work scope
transitivity; no response or task attachment is changed.
-/
theorem Under.mono {base next} {completed : Completion α} (under : Under next completed)
    (below : base.IsPrefix next)
    : Under base completed :=
  ⟨under.1, under.2.mono below⟩

/-- Pure completions retain no work or scope obligations. -/
theorem pure (base : ResponsePath) (value : α) : Under base (Completion.pure value) :=
  ⟨trivial, trivial⟩

/-- Failed completions retain no work or scope obligations. -/
theorem error (base : ResponsePath) (errors : Nat)
    : Under base (Completion.error errors : Completion α) :=
  ⟨trivial, trivial⟩

/-- Combining completions retains certified components or discards all work on failure.
Witness: the two result constructors and the work-combine certificate.
-/
theorem combine (base : ResponsePath) (f : α → β → γ)
    (left : Completion α) (right : Completion β)
    (hl : Under base left) (hr : Under base right)
    : Under base (Completion.combine f left right) := by
  simp only [Under] at hl hr
  cases he : left.result <;> cases ht : right.result <;>
    simp [Completion.combine, he, ht, GraphQL.Execution.Result.combine, Completion.error,
      Under, WorkScoped, ScopesUnder, hl, hr]

/-- Mapping values preserves successful work and discards bubbling work. -/
theorem map (base : ResponsePath) (f : α → β) (completed : Completion α)
    (h : Under base completed)
    : Under base (completed.map f) := by
  simp only [Under] at h
  cases he : completed.result <;>
    simp [Completion.map, he, Completion.error, Under, WorkScoped, ScopesUnder, h]

/-- Null catching preserves successful work and discards bubbling work. -/
theorem catchNull (base : ResponsePath) (f : α → ResponseValue) (completed : Completion α)
    (h : Under base completed)
    : Under base (completed.catchNull f) := by
  simp only [Under] at h
  cases he : completed.result <;>
    simp [Completion.catchNull, he, Under, WorkScoped, ScopesUnder, h]

/-- Non-null completion retains the certificate or discards work on bubbling. -/
theorem nonNull (base : ResponsePath) (completed : Completion ResponseValue)
    (h : Under base completed)
    : Under base completed.nonNull := by
  unfold Completion.nonNull
  split
  · simp [Under, Completion.error, WorkScoped, ScopesUnder]
  · exact h

end GraphQL.IncrementalDelivery.Correctness.ScopeMetadata
