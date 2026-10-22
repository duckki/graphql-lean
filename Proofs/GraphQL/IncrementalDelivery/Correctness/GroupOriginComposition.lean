import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupProducerOrigins
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence

/-! Group origins survive structural composition without changing node or payload paths. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics

namespace GroupOriginComposition

/-- Empty work has no descendant locations.
Witness: every non-root navigation rule requires a nonempty constructor.
-/
theorem located_empty {address current producer owners}
    (known : StructuralEquivalence.Located .empty address current producer owners)
    : current = .empty := by
  induction known with
  | root => rfl
  | left _ ih | right _ ih | executionGroup _ ih | item _ _ ih => cases ih

/-- Empty work has no group descriptor.
Witness: a containing execution-group location would contradict empty-work navigation.
-/
theorem no_group_empty {node dependencies producer}
    (known : NodeAt .empty node .group dependencies producer)
    : False := by
  obtain ⟨address, groups, path, result, children, owners, group, located, _⟩ := known
  cases located_empty (StructuralEquivalence.located_of_current located)

/-- Relocate a task occurrence under a structural route; item ordinals are unchanged. -/
def relocate (route : Address) : Occurrence → Occurrence
  | .executionGroup address => .executionGroup (route ++ address)
  | .item address index => .item (route ++ address) index

/-- Retain an internal producer, or use the enclosing producer for a local root. -/
def reparent (route : Address) (enclosing : Option Occurrence)
    (producer : Option Occurrence)
    : Option Occurrence :=
  producer.map (relocate route) |>.or enclosing

/-- A root inherits the enclosing owners; an internally produced location keeps its own.
-/
def enclosingOwners (enclosing owners : NodeRefs) (producer : Option Occurrence)
    : NodeRefs :=
  if producer.isNone then enclosing else owners

-----------------------------------------------------------------------------------------
-- Exact producer transport
-----------------------------------------------------------------------------------------

/-- Embedding retains the same producer edge, with both endpoints relocated together.
Witness: structural navigation induction; only a local root acquires the enclosing edge.
-/
theorem located_embed {work address current producer owners}
    (known : StructuralEquivalence.Located work address current producer owners)
    {root route parent refs}
    (embedded
      : StructuralEquivalence.Located root route work.withoutDeclarations parent refs)
    : StructuralEquivalence.Located root (route ++ address) current
        (reparent route parent producer) (enclosingOwners refs owners producer) := by
  induction known with
  | root => simpa [reparent, enclosingOwners] using embedded
  | left _ ih => simpa [List.append_assoc] using ih.left
  | right _ ih => simpa [List.append_assoc] using ih.right
  | executionGroup _ ih =>
      simpa [reparent, relocate, enclosingOwners, List.append_assoc]
        using ih.executionGroup
  | item _ entry ih =>
      simpa [reparent, relocate, enclosingOwners, List.append_assoc] using ih.item entry

/-- A task's owners and payload survive embedding along with its exact relocated producer.
Witness: the same group or indexed stream entry at the transported location.
-/
theorem task_embed {work occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload) {root route parent refs}
    (embedded : Located root route work.withoutDeclarations parent refs)
    : TaskAt root (relocate route occurrence) owners (reparent route parent producer)
        payload := by
  have base := StructuralEquivalence.located_of_current embedded
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      exact (StructuralEquivalence.TaskAt.executionGroup (located_embed located base)).toCurrent
  | item located entry =>
      exact (StructuralEquivalence.TaskAt.item (located_embed located base) entry).toCurrent

/-- Group metadata is unchanged by embedding; birth is the exact transported producer.
Witness: retain the same deferred-fragment member at its relocated task location.
-/
theorem group_embed {work node dependencies producer}
    (known : NodeAt work node .group dependencies producer) {root route parent refs}
    (embedded : Located root route work.withoutDeclarations parent refs)
    : NodeAt root node .group dependencies (reparent route parent producer) := by
  obtain ⟨address, groups, path, result, children, owners, group, located, member,
    rfl, rfl⟩ := known
  exact (StructuralEquivalence.NodeAt.group
    (located_embed (StructuralEquivalence.located_of_current located)
      (StructuralEquivalence.located_of_current embedded)) member).toCurrent

-----------------------------------------------------------------------------------------
-- Recovering a component's descriptors
-----------------------------------------------------------------------------------------

/-- Every non-root location in combined work belongs to one of its components.
Witness: navigation induction, discarding only the leading left/right route.
-/
theorem located_component {left right address current producer owners}
    (known
      : StructuralEquivalence.Located (.combine left right) address current producer
          owners)
    : current = .combine left right
      ∨ (∃ address producer owners,
          StructuralEquivalence.Located left address current producer owners)
      ∨ (∃ address producer owners,
          StructuralEquivalence.Located right address current producer owners) := by
  induction known with
  | root => exact Or.inl rfl
  | left _ ih =>
      rcases ih with same | ⟨address, producer, owners, found⟩
        | ⟨address, producer, owners, found⟩
      · cases same
        exact Or.inr (Or.inl ⟨[], none, [], .root⟩)
      · exact Or.inr (Or.inl ⟨_, _, _, found.left⟩)
      · exact Or.inr (Or.inr ⟨_, _, _, found.left⟩)
  | right _ ih =>
      rcases ih with same | ⟨address, producer, owners, found⟩
        | ⟨address, producer, owners, found⟩
      · cases same
        exact Or.inr (Or.inr ⟨[], none, [], .root⟩)
      · exact Or.inr (Or.inl ⟨_, _, _, found.right⟩)
      · exact Or.inr (Or.inr ⟨_, _, _, found.right⟩)
  | executionGroup _ ih =>
      rcases ih with impossible | ⟨address, producer, owners, found⟩
        | ⟨address, producer, owners, found⟩
      · cases impossible
      · exact Or.inr (Or.inl ⟨_, _, _, found.executionGroup⟩)
      · exact Or.inr (Or.inr ⟨_, _, _, found.executionGroup⟩)
  | item _ entry ih =>
      rcases ih with impossible | ⟨address, producer, owners, found⟩
        | ⟨address, producer, owners, found⟩
      · cases impossible
      · exact Or.inr (Or.inl ⟨_, _, _, found.item entry⟩)
      · exact Or.inr (Or.inr ⟨_, _, _, found.item entry⟩)

/-- A group descriptor in combined work comes from one component, with identical metadata.
Witness: component location recovery and the original fragment member.
-/
theorem group_component {left right node dependencies producer}
    (known : NodeAt (.combine left right) node .group dependencies producer)
    : (∃ producer, NodeAt left node .group dependencies producer)
      ∨ (∃ producer, NodeAt right node .group dependencies producer) := by
  obtain ⟨address, groups, path, result, children, owners, group, located, member,
    rfl, rfl⟩ := known
  rcases located_component (StructuralEquivalence.located_of_current located) with
    impossible | ⟨address, producer, owners, found⟩ | ⟨address, producer, owners, found⟩
  · cases impossible
  · exact Or.inl ⟨_, (StructuralEquivalence.NodeAt.group found member).toCurrent⟩
  · exact Or.inr ⟨_, (StructuralEquivalence.NodeAt.group found member).toCurrent⟩

/-- A location in an execution-group wrapper is its root or belongs to its child work.
Witness: navigation induction; the first producer edge enters the children.
-/
theorem located_group_component
    {groups path result children address current producer owners}
    (known
      : StructuralEquivalence.Located (.executionGroup groups path result children)
          address current producer owners)
    : current = .executionGroup groups path result children
      ∨ ∃ address producer owners,
          StructuralEquivalence.Located children address current producer owners := by
  induction known with
  | root => exact Or.inl rfl
  | left _ ih =>
      rcases ih with impossible | ⟨address, producer, owners, found⟩
      · cases impossible
      · exact Or.inr ⟨_, _, _, found.left⟩
  | right _ ih =>
      rcases ih with impossible | ⟨address, producer, owners, found⟩
      · cases impossible
      · exact Or.inr ⟨_, _, _, found.right⟩
  | executionGroup _ ih =>
      rcases ih with same | ⟨address, producer, owners, found⟩
      · cases same
        exact Or.inr ⟨[], none, [], .root⟩
      · exact Or.inr ⟨_, _, _, found.executionGroup⟩
  | item _ entry ih =>
      rcases ih with impossible | ⟨address, producer, owners, found⟩
      · cases impossible
      · exact Or.inr ⟨_, _, _, found.item entry⟩

/-- A wrapper's group descriptor is a root member or a descriptor of its child work.
Witness: recover the containing location and retain its fragment metadata.
-/
theorem group_in_executionGroup {groups path result children node dependencies producer}
    (known
      : NodeAt (.executionGroup groups path result children) node .group dependencies
          producer)
    : (∃ group ∈ groups,
        node = group.node ∧ dependencies = group.ancestors.map DeliveryNode.ref)
      ∨ ∃ producer, NodeAt children node .group dependencies producer := by
  obtain ⟨address, fragments, attachment, outcome, nested, owners, group, located, member,
    rfl, rfl⟩ := known
  rcases located_group_component (StructuralEquivalence.located_of_current located) with
    same | ⟨address, producer, owners, found⟩
  · cases same
    exact Or.inl ⟨group, member, rfl, rfl⟩
  · exact Or.inr ⟨_, (StructuralEquivalence.NodeAt.group found member).toCurrent⟩

/-- A stream location is its root or a descendant of one actual indexed item's work.
Witness: navigation induction, retaining the first item entry and its ordinal.
-/
theorem located_stream_component {node items address current producer owners}
    (known
      : StructuralEquivalence.Located (.stream node items) address current producer
          owners)
    : current = .stream node items
      ∨ ∃ (index : Nat) (result : TaskOutcome ResponseValue) (children : Work)
          (address : Address) (producer : Option Occurrence) (owners : NodeRefs),
          items[index]? = some (result, children)
          ∧ StructuralEquivalence.Located children address current producer owners := by
  induction known with
  | root => exact Or.inl rfl
  | left _ ih =>
      rcases ih with impossible | ⟨index, result, children, address, producer, owners,
        entry, found⟩
      · cases impossible
      · exact Or.inr ⟨_, _, _, _, _, _, entry, found.left⟩
  | right _ ih =>
      rcases ih with impossible | ⟨index, result, children, address, producer, owners,
        entry, found⟩
      · cases impossible
      · exact Or.inr ⟨_, _, _, _, _, _, entry, found.right⟩
  | executionGroup _ ih =>
      rcases ih with impossible | ⟨index, result, children, address, producer, owners,
        entry, found⟩
      · cases impossible
      · exact Or.inr ⟨_, _, _, _, _, _, entry, found.executionGroup⟩
  | item _ selected ih =>
      rcases ih with same | ⟨index, result, children, address, producer, owners, entry,
        found⟩
      · cases same
        exact Or.inr ⟨_, _, _, [], none, [], selected, .root⟩
      · exact Or.inr ⟨_, _, _, _, _, _, entry, found.item selected⟩

/-- A stream's group descriptors come from indexed item work, never its stream root.
Witness: recover an actual item entry and retain its deferred-fragment member.
-/
theorem group_in_stream {stream items node dependencies producer}
    (known : NodeAt (.stream stream items) node .group dependencies producer)
    : ∃ (index : Nat) (result : TaskOutcome ResponseValue) (children : Work)
        (producer : Option Occurrence),
        items[index]? = some (result, children)
        ∧ NodeAt children node .group dependencies producer := by
  obtain ⟨address, groups, path, result, children, owners, group, located, member,
    rfl, rfl⟩ := known
  rcases located_stream_component (StructuralEquivalence.located_of_current located) with
    impossible | ⟨index, result, children, address, producer, owners, entry, found⟩
  · cases impossible
  · exact ⟨_, _, _, _, entry, (StructuralEquivalence.NodeAt.group found member).toCurrent⟩

end GroupOriginComposition

-----------------------------------------------------------------------------------------
-- Compositional structural origins
-----------------------------------------------------------------------------------------

/-- A single ref's root or scope-covering introducing producer; other refs are irrelevant.
-/
def GroupOrigin (work : Work) (ref : NodeRef) : Prop :=
  ∃ origin parents producer,
    NodeAt work origin .group parents producer
    ∧ origin.ref = ref
    ∧ (producer = none
        ∨ ∃ source owners ancestor payload ref,
            producer = some source
            ∧ TaskAt work source owners ancestor payload
            ∧ ref ∈ owners
            ∧ ref < origin.ref
            ∧ payload.path.IsPrefix origin.path)

/-- Inherited refs may have origins outside this component; all other group refs have local
origins. This is an execution-induction certificate, not a queue admission premise.
-/
def GroupOriginsExcept (inherited : NodeRefs) (work : Work) : Prop :=
  ∀ node dependencies producer,
    NodeAt work node .group dependencies producer
    → node.ref ∈ inherited ∨ GroupOrigin work node.ref

/-- Empty work satisfies any inherited-ref certificate.
Witness: there are no group descriptors to justify.
-/
theorem GroupOriginsExcept.empty (inherited : NodeRefs)
    : GroupOriginsExcept inherited .empty :=
  fun _ _ _ known => (GroupOriginComposition.no_group_empty known).elim

/-- A complete certificate supplies an origin for every known group descriptor.
Witness: specialize its defining quantifiers.
-/
theorem GroupProducerOrigins.origin {work node dependencies producer}
    (origins : GroupProducerOrigins work)
    (known : NodeAt work node .group dependencies producer)
    : GroupOrigin work node.ref :=
  origins _ _ _ known

/-- Root-free embedding transports an origin's producer and descriptor together.
Witness: exact location and task relocation; attachment paths and owner refs are fixed.
-/
theorem GroupOrigin.embed {work root route ref} (origin : GroupOrigin work ref)
    (embedded : Located root route work.withoutDeclarations none [])
    : GroupOrigin root ref := by
  obtain ⟨node, parents, producer, known, same, supported⟩ := origin
  refine ⟨node, parents, _, GroupOriginComposition.group_embed known embedded, same, ?_⟩
  rcases supported with root | ⟨source, owners, ancestor, payload, ref, rfl,
    task, member, earlier, below⟩
  · left
    simp [root, GroupOriginComposition.reparent]
  · right
    refine ⟨GroupOriginComposition.relocate route source, owners,
      GroupOriginComposition.reparent route none ancestor, payload, ref, ?_,
      GroupOriginComposition.task_embed task embedded, member, earlier, below⟩
    simp [GroupOriginComposition.reparent]

/-- Adding a right component preserves a left-hand origin.
Witness: root-free embedding at the left edge, retaining the same group ref.
-/
theorem GroupOrigin.combine_left {work ref} (origin : GroupOrigin work ref) (right : Work)
    : GroupOrigin (.combine work right) ref :=
  origin.embed (Located.left (root := .combine work right) Located.root)

/-- Adding a left component preserves a right-hand origin.
Witness: root-free embedding at the right edge, retaining the same group ref.
-/
theorem GroupOrigin.combine_right {work ref} (origin : GroupOrigin work ref) (left : Work)
    : GroupOrigin (.combine left work) ref :=
  origin.embed (Located.right (root := .combine left work) Located.root)

/-- Complete origins also give a component certificate with any inherited refs.
Witness: every descriptor takes the locally witnessed alternative.
-/
theorem GroupProducerOrigins.except {work} (origins : GroupProducerOrigins work)
    (inherited : NodeRefs)
    : GroupOriginsExcept inherited work :=
  fun _ _ _ known => Or.inr (origins.origin known)

/-- Discharging inherited refs inside the same work yields a complete certificate.
Witness: use the supplied origin only when the component certificate takes its exception.
-/
theorem GroupOriginsExcept.resolve {inherited work}
    (origins : GroupOriginsExcept inherited work)
    (inheritedOrigins : ∀ ref ∈ inherited, GroupOrigin work ref)
    : GroupProducerOrigins work := by
  intro node dependencies producer known
  rcases origins _ _ _ known with external | localOrigin
  · exact inheritedOrigins _ external
  · exact localOrigin

/-- Components with the same inherited refs retain their local origins when combined.
Witness: recover the descriptor's component and embed its origin, leaving exceptions alone.
-/
theorem GroupOriginsExcept.combine {inherited left right}
    (leftOrigins : GroupOriginsExcept inherited left)
    (rightOrigins : GroupOriginsExcept inherited right)
    : GroupOriginsExcept inherited (.combine left right) := by
  intro node dependencies producer known
  rcases GroupOriginComposition.group_component known with ⟨birth, component⟩
    | ⟨birth, component⟩
  · exact (leftOrigins _ _ _ component).imp_right (fun origin => origin.combine_left right)
  · exact (rightOrigins _ _ _ component).imp_right (fun origin => origin.combine_right left)

/-- Earlier work discharges newly inherited refs in a later component.
Witness: reuse the earlier origin for matching refs; otherwise retain a local origin or
the common inherited exception. A narrower reused producer need not cover the old scope.
-/
theorem GroupOriginsExcept.combine_resolving {inherited introduced left right}
    (leftOrigins : GroupOriginsExcept inherited left)
    (rightOrigins : GroupOriginsExcept (inherited ++ introduced) right)
    (introducedOrigins : ∀ ref ∈ introduced, GroupOrigin left ref)
    : GroupOriginsExcept inherited (.combine left right) := by
  intro node dependencies producer known
  rcases GroupOriginComposition.group_component known with ⟨birth, component⟩
    | ⟨birth, component⟩
  · exact (leftOrigins _ _ _ component).imp_right (fun origin => origin.combine_left right)
  · rcases rightOrigins _ _ _ component with inheritedRef | localOrigin
    · rcases List.mem_append.mp inheritedRef with old | fresh
      · exact Or.inl old
      · exact Or.inr ((introducedOrigins _ fresh).combine_left right)
    · exact Or.inr (localOrigin.combine_right left)

/-- A root execution-group member has an origin without an introducing producer.
Witness: its descriptor at the empty structural route.
-/
theorem GroupOrigin.executionGroup_root {groups path result children group}
    (member : group ∈ groups)
    : GroupOrigin (.executionGroup groups path result children) group.node.ref :=
  ⟨
    group.node,
    group.ancestors.map DeliveryNode.ref,
    none,
    NodeAt.group Located.root member,
    rfl,
    Or.inl rfl
  ⟩

/-- Wrapping child work preserves local origins, subject only to the new producer boundary.
Witness: a reused wrapper ref chooses its root descriptor; another child root acquires
the wrapper task's earlier, scope-covering owner. Internal producers relocate unchanged.
Inherited refs remain explicit exceptions for an enclosing composition to discharge.
-/
theorem GroupOriginsExcept.executionGroup {inherited groups path result children}
    (origins : GroupOriginsExcept inherited children)
    (rootSupport
      : ∀ node dependencies,
          NodeAt children node .group dependencies none
          → node.ref ∉ inherited
          → (∃ group ∈ groups, group.node.ref = node.ref)
            ∨ ∃ ref ∈ groups.map (fun group => group.node.ref),
                ref < node.ref ∧ path.IsPrefix node.path)
    : GroupOriginsExcept inherited (.executionGroup groups path result children) := by
  intro node dependencies producer known
  rcases GroupOriginComposition.group_in_executionGroup known with
    ⟨group, member, rfl, rfl⟩ | ⟨birth, component⟩
  · exact Or.inr (GroupOrigin.executionGroup_root member)
  · rcases origins _ _ _ component with inheritedRef | localOrigin
    · exact Or.inl inheritedRef
    · by_cases inheritedRef : node.ref ∈ inherited
      · exact Or.inl inheritedRef
      obtain ⟨origin, parents, birth, originKnown, same, supported⟩ := localOrigin
      have embedded : Located (.executionGroup groups path result children) [0] children.withoutDeclarations
          (some (.executionGroup [])) (groups.map (fun group => group.node.ref)) :=
        Located.executionGroup (root := .executionGroup groups path result children) Located.root
      have descriptor := GroupOriginComposition.group_embed originKnown embedded
      rcases supported with root | ⟨source, owners, ancestor, payload, ref, rfl,
        task, member, earlier, below⟩
      · subst birth
        rcases rootSupport _ _ originKnown (by simpa only [same] using inheritedRef) with
          ⟨group, member, equalRef⟩
          | ⟨ref, member, earlier, below⟩
        · obtain ⟨node', parents', birth', known', same', supported'⟩ :=
            GroupOrigin.executionGroup_root (path := path) (result := result)
              (children := children) member
          exact Or.inr ⟨node', parents', birth', known', same'.trans (equalRef.trans same),
            supported'⟩
        · refine Or.inr ⟨origin, parents, _, descriptor, same, Or.inr ?_⟩
          exact ⟨.executionGroup [], groups.map (fun group => group.node.ref), none,
            .object path result.deliveryResult, ref, rfl, TaskAt.executionGroup Located.root,
            member, earlier, below⟩
      · refine Or.inr ⟨origin, parents, _, descriptor, same, Or.inr ?_⟩
        refine ⟨GroupOriginComposition.relocate [0] source, owners,
          GroupOriginComposition.reparent [0] (some (.executionGroup [])) ancestor,
          payload, ref, ?_, GroupOriginComposition.task_embed task embedded,
          member, earlier, below⟩
        simp [GroupOriginComposition.reparent]

/-- Stream-item work preserves group origins across the item producer boundary.
Witness: a child root acquires the indexed item task's earlier stream ref and covering
list attachment. Already introduced child groups keep their relocated internal producer.
Empty streams have no group-origin obligations.
-/
theorem GroupProducerOrigins.stream {stream items}
    (origins
      : ∀ (index : Nat) (result : TaskOutcome ResponseValue) children,
          items[index]? = some (result, children) → GroupProducerOrigins children)
    (rootSupport
      : ∀ (index : Nat) (result : TaskOutcome ResponseValue) children node dependencies,
          items[index]? = some (result, children)
          → NodeAt children node .group dependencies none
          → stream.ref < node.ref ∧ stream.path.IsPrefix node.path)
    : GroupProducerOrigins (.stream stream items) := by
  intro node dependencies producer known
  obtain ⟨index, result, children, birth, entry, component⟩ :=
    GroupOriginComposition.group_in_stream known
  obtain ⟨origin, parents, birth, originKnown, same, supported⟩ :=
    origins _ _ _ entry _ _ _ component
  have embedded : Located (.stream stream items) [index] children.withoutDeclarations
      (some (.item [] index)) [] := Located.item (root := .stream stream items) Located.root entry
  refine ⟨origin, parents, _, GroupOriginComposition.group_embed originKnown embedded,
    same, Or.inr ?_⟩
  rcases supported with root | ⟨source, owners, ancestor, payload, ref, rfl,
    task, member, earlier, below⟩
  · subst birth
    have support := rootSupport _ _ _ _ _ entry originKnown
    exact ⟨.item [] index, [stream.ref], none, .item stream result.deliveryResult, stream.ref, rfl,
      TaskAt.item Located.root entry, by simp, support.1, support.2⟩
  · refine ⟨GroupOriginComposition.relocate [index] source, owners,
      GroupOriginComposition.reparent [index] (some (.item [] index)) ancestor,
      payload, ref, ?_, GroupOriginComposition.task_embed task embedded,
      member, earlier, below⟩
    simp [GroupOriginComposition.reparent]

/-- Combined components retain their origin certificates, even when they share group refs.
Witness: choose the component of the descriptor, then relocate its origin and producer
together. No completion order, notice, or failure-report premise is required.
-/
theorem GroupProducerOrigins.combine {left right : Work}
    (leftOrigins : GroupProducerOrigins left) (rightOrigins : GroupProducerOrigins right)
    : GroupProducerOrigins (.combine left right) := by
  apply ((leftOrigins.except []).combine (rightOrigins.except [])).resolve
  simp

end GraphQL.IncrementalDelivery.Correctness
