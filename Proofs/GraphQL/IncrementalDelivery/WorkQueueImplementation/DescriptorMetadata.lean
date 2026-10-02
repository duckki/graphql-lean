import GraphQL.IncrementalDelivery.WorkQueueSemantics
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CollectedDescriptorLabels
import Proofs.GraphQL.IncrementalDelivery.Semantics.OwnerMetadata

/-! One ghost assignment records complete delivery descriptors, including ancestors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Proof-only coherence: equal keys in `work` identify equal full node descriptors.
Derived from generated work by `ExecutedWork.nodeKeyCoherent` in `GeneratedDescriptors`;
not a public scheduler or event-source premise.
-/
def NodeKeyCoherent (work : Execution.Work) : Prop :=
  ∀ first firstKind firstDependencies firstProducer
    second secondKind secondDependencies secondProducer,
    NodeAt work first firstKind firstDependencies firstProducer
    → NodeAt work second secondKind secondDependencies secondProducer
    → first.key = second.key
    → first = second

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.DescriptorMetadata
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics.OwnerPaths (mapNodes fragmentNodes)

/-- Proof-only complete descriptor associated with each allocated execution key. -/
abbrev Assignment := Nat → DeliveryNode

/-- `next` preserves every descriptor allocated before `bound`. -/
def Extends (bound : Nat) (old next : Assignment) : Prop :=
  ∀ key < bound, next key = old key

/-- `node` is allocated below `bound` and agrees with its complete assigned descriptor. -/
def Assigned (nodes : Assignment) (bound : Nat) (node : DeliveryNode) : Prop :=
  node.key < bound ∧ nodes node.key = node

/-- Contributor and ancestor descriptors in `deferMap` share one allocation assignment. -/
def MapAt (nodes : Assignment) (bound : Nat) (deferMap : DeferMap) : Prop :=
  ∀ node ∈ mapNodes deferMap, Assigned nodes bound node

/-- All descriptors throughout finite work agree with one assignment, including taskless
defer ancestors and work produced by streamed items.
-/
def WorkAt (nodes : Assignment) (bound : Nat) : Work → Prop
  | .empty => True
  | .combine left right => WorkAt nodes bound left ∧ WorkAt nodes bound right
  | .executionGroup groups _ _ children =>
      MapAt nodes bound groups ∧ WorkAt nodes bound children
  | .stream node items =>
      Assigned nodes bound node ∧ ∀ item ∈ items, WorkAt nodes bound item.2
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

/-- Every item's child work has descriptors from the same assignment. -/
def ItemsAt (nodes : Assignment) (bound : Nat)
    (items : List (GraphQL.Execution.Result ResponseValue × Work))
    : Prop :=
  ∀ item ∈ items, WorkAt nodes bound item.2

/-- Execution extends its assignment without changing previously allocated descriptors. -/
def Output (nodes : Assignment) (start : Nat) (work : Work) (finish : Nat) : Prop :=
  start ≤ finish ∧ ∃ next, Extends start nodes next ∧ WorkAt next finish work

/-- A completion's work and final counter carry the extended descriptor certificate. -/
def Completed (nodes : Assignment) (start : Nat) (output : Completion α × Nat) : Prop :=
  Output nodes start output.1.work output.2

/-- Stream-item completion extends the same assignment across all generated child work. -/
def ItemsOutput (nodes : Assignment) (start : Nat)
    (output : List (GraphQL.Execution.Result ResponseValue × Work) × Nat)
    : Prop :=
  start ≤ output.2 ∧ ∃ next, Extends start nodes next ∧ ItemsAt next output.2 output.1

/-- An assignment preserves itself. Witness: reflexivity at each key. -/
theorem Extends.refl (bound : Nat) (nodes : Assignment) : Extends bound nodes nodes :=
  fun _ _ => rfl

/-- Successive allocation extensions preserve the original prefix.
Witness: compose the pointwise equalities below the earlier bound.
-/
theorem Extends.trans {first middle last : Assignment} {start finish : Nat}
    (before : Extends start first middle) (after : Extends finish middle last)
    (bound : start ≤ finish)
    : Extends start first last := by
  intro key earlier
  exact (after key (by omega)).trans (before key earlier)

/-- An old descriptor remains assigned after further allocation.
Witness: its key is below the preserved prefix.
-/
theorem Assigned.extend {nodes next : Assignment} {start finish : Nat}
    {node : DeliveryNode} (known : Assigned nodes start node)
    (extension : Extends start nodes next) (bound : start ≤ finish)
    : Assigned next finish node :=
  ⟨Nat.lt_of_lt_of_le known.1 bound, (extension node.key known.1).trans known.2⟩

/-- Extending allocation preserves every descriptor in an existing defer map.
Witness: apply descriptor preservation pointwise, including ancestors.
-/
theorem MapAt.extend {nodes next : Assignment} {start finish : Nat} {deferMap : DeferMap}
    (known : MapAt nodes start deferMap) (extension : Extends start nodes next)
    (bound : start ≤ finish)
    : MapAt next finish deferMap :=
  fun node member => (known node member).extend extension bound

/-- Extending allocation preserves descriptors recursively throughout existing work.
Witness: structural work induction and pointwise preservation in each stream item.
-/
theorem WorkAt.extend {nodes next : Assignment} {start finish : Nat} {work : Work}
    (known : WorkAt nodes start work) (extension : Extends start nodes next)
    (bound : start ≤ finish)
    : WorkAt next finish work := by
  cases work with
  | empty => simp [WorkAt]
  | combine left right =>
      simp only [WorkAt] at known ⊢
      exact ⟨known.1.extend extension bound, known.2.extend extension bound⟩
  | executionGroup groups path result children =>
      simp only [WorkAt] at known ⊢
      exact ⟨known.1.extend extension bound, known.2.extend extension bound⟩
  | stream node items =>
      simp only [WorkAt] at known ⊢
      exact ⟨known.1.extend extension bound, fun item member =>
        (known.2 item member).extend extension bound⟩
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem member
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

/-- Selecting contributor fragments preserves every retained descriptor.
Witness: each successful lookup returns a member of the original map.
-/
theorem mapAt_filterMap {nodes : Assignment} {bound : Nat} {deferMap : DeferMap}
    (known : MapAt nodes bound deferMap) (keys : List Nat)
    : MapAt nodes bound (keys.filterMap (lookupDeferredFragment? deferMap)) := by
  intro node member
  obtain ⟨fragment, fragmentMember, within⟩ := List.mem_flatMap.mp member
  obtain ⟨key, _, found⟩ := List.mem_filterMap.mp fragmentMember
  exact known node (List.mem_flatMap.mpr
    ⟨fragment, List.mem_of_find?_eq_some found, within⟩)

/-- Installing fresh usages assigns exact new descriptors and preserves existing ones.
Witness: fresh keys are disjoint from the old prefix; coherent labels identify each
lookup-selected usage, and ancestor descriptors are copied from the current defer map.
-/
theorem mapAt_new (nodes : Assignment) (start finish : Nat) (path : ResponsePath)
    (deferMap : DeferMap) (usages : List DeferUsage)
    (known : MapAt nodes start deferMap) (bound : start ≤ finish)
    (fresh : ∀ usage ∈ usages, start ≤ usage.key ∧ usage.key < finish)
    (labels : LabelsCoherent usages)
    : ∃ next,
        Extends start nodes next
        ∧ MapAt next finish (getNewDeferMap usages path deferMap) := by
  let next : Assignment := fun key =>
    match usages.find? (fun usage => usage.key == key) with
    | none => nodes key
    | some usage => { key, path, label := usage.label }
  have extension : Extends start nodes next := by
    intro key below
    unfold next
    cases found : usages.find? (fun usage => usage.key == key) with
    | none => rfl
    | some usage =>
        have member := List.mem_of_find?_eq_some found
        have equal := beq_iff_eq.mp
          (List.find?_some (p := fun usage : DeferUsage => usage.key == key) found)
        have := (fresh usage member).1
        omega
  have newAssigned (usage : DeferUsage) (member : usage ∈ usages)
      : Assigned next finish { key := usage.key, path, label := usage.label } := by
    refine ⟨(fresh usage member).2, ?_⟩
    unfold next
    cases found : usages.find? (fun candidate => candidate.key == usage.key) with
    | none =>
        have missing := List.find?_eq_none.mp found usage member
        simp at missing
    | some candidate =>
        have equal := beq_iff_eq.mp (List.find?_some
          (p := fun candidate : DeferUsage => candidate.key == usage.key) found)
        have label := labels candidate (List.mem_of_find?_eq_some found) usage member equal
        simp only [label]
  refine ⟨next, extension, ?_⟩
  have loop (more : List DeferUsage) (subset : more.Subset usages) (current : DeferMap)
      (assigned : MapAt next finish current)
      : MapAt next finish (getNewDeferMap more path current) := by
    induction more generalizing current with
    | nil => exact assigned
    | cons usage rest ih =>
        unfold getNewDeferMap
        rw [List.foldl_cons]
        apply ih (fun _ h => subset (List.mem_cons_of_mem _ h))
        intro node member
        simp only [mapNodes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.mem_append, fragmentNodes, List.mem_cons] at member
        rcases member with old | rfl | ancestor
        · exact assigned node old
        · exact newAssigned usage (subset List.mem_cons_self)
        · obtain ⟨key, _, found⟩ := List.mem_filterMap.mp ancestor
          obtain ⟨fragment, located, same⟩ := Option.map_eq_some_iff.mp found
          subst node
          exact assigned fragment.node (List.mem_flatMap.mpr
            ⟨fragment, List.mem_of_find?_eq_some located, List.mem_cons_self⟩)
  exact loop usages (fun _ h => h) deferMap (known.extend extension bound)

/-- Empty work preserves its assignment and counter. Witness: the empty certificate. -/
theorem output_empty (nodes : Assignment) (state : Nat)
    : Output nodes state .empty state :=
  ⟨Nat.le_refl _, nodes, Extends.refl _ _, by simp [WorkAt]⟩

/-- Combining completions retains descriptor metadata in all surviving work.
Witness: the result cases either combine both work trees or discard work on error.
-/
theorem workAt_completionCombine (nodes : Assignment) (bound : Nat) (f : α → β → γ)
    (left : Completion α) (right : Completion β)
    (hl : WorkAt nodes bound left.work) (hr : WorkAt nodes bound right.work)
    : WorkAt nodes bound (Completion.combine f left right).work := by
  cases hlr : left.result <;> cases hrr : right.result <;>
    simp [Completion.combine, GraphQL.Execution.Result.combine, hlr, hrr,
      Completion.error, WorkAt, hl, hr]

/-- Mapping response data preserves or discards work without changing its descriptors.
Witness: case analysis on the completion result.
-/
theorem workAt_map (nodes : Assignment) (bound : Nat) (f : α → β)
    (completed : Completion α) (known : WorkAt nodes bound completed.work)
    : WorkAt nodes bound (completed.map f).work := by
  cases result : completed.result <;> simp [Completion.map, result, Completion.error,
    WorkAt, known]

/-- Catching a bubbling null preserves descriptors in any retained work.
Witness: case analysis on the completion result.
-/
theorem workAt_catchNull (nodes : Assignment) (bound : Nat) (f : α → ResponseValue)
    (completed : Completion α) (known : WorkAt nodes bound completed.work)
    : WorkAt nodes bound (completed.catchNull f).work := by
  cases result : completed.result <;> simp [Completion.catchNull, result, WorkAt, known]

/-- Non-null propagation never invents a descriptor.
Witness: the non-null check either retains the original work or discards it.
-/
theorem workAt_nonNull (nodes : Assignment) (bound : Nat)
    (completed : Completion ResponseValue) (known : WorkAt nodes bound completed.work)
    : WorkAt nodes bound completed.nonNull.work := by
  unfold Completion.nonNull
  split <;> simp [Completion.error, WorkAt, known]

/-- Allocating one stream key extends the assignment with its exact descriptor.
Witness: replace only the next fresh key, outside the already allocated prefix.
-/
theorem assigned_fresh (nodes : Assignment) (state : Nat) (node : DeliveryNode)
    (key : node.key = state)
    : let next := fun key => if key = state then node else nodes key
      Extends state nodes next ∧ Assigned next (state + 1) node := by
  refine ⟨?_, ?_⟩
  · intro key below
    simp [show key ≠ state by omega]
  · simp [Assigned, key]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.DescriptorMetadata
