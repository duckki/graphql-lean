import Proofs.GraphQL.IncrementalDelivery.Correctness.ExecutedScopes
import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferDependencies

/-! Producer support preserves owner notice scopes, even with narrower task attachments. -/

namespace GraphQL.IncrementalDelivery.Correctness.ScopeMetadata
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling WorkQueueSemantics

/-- Removing outer declaration metadata retains coherent task scopes. -/
theorem WorkScoped.withoutDeclarations {work} (known : WorkScoped work)
    : WorkScoped work.withoutDeclarations := by
  cases work with
  | declareGroups groups tasks =>
      rw [WorkScoped] at known
      exact known.2.withoutDeclarations
  | _ => exact known
termination_by work

/-- Removing outer declarations retains the lower bound on task scopes. -/
theorem ScopesUnder.withoutDeclarations {base work} (known : ScopesUnder base work)
    : ScopesUnder base work.withoutDeclarations := by
  cases work with
  | declareGroups groups tasks =>
      rw [ScopesUnder] at known
      exact known.2.withoutDeclarations
  | _ => exact known
termination_by work

/-- An indexed child inherits its stream-boundary scope certificate.
Witness: list membership descent through coherent item work.
-/
theorem ItemsScoped.member {base items} (certified : ItemsScoped base items)
    {result children} (member : (result, children) ∈ items)
    : WorkScoped children ∧ ScopesUnder base children := by
  induction items with
  | nil => cases member
  | cons entry rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst entry
        exact certified.1
      · exact ih certified.2 later

/-- Scope coherence is retained by every structurally located subtree.
Witness: navigation through components, deferred children, and actual item entries.
-/
theorem WorkScoped.located {work address current producer enclosing}
    (certified : WorkScoped work)
    (located : Located work address current producer enclosing)
    : WorkScoped current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact certified.withoutDeclarations
  | left _ ih => exact ih.1.withoutDeclarations
  | right _ ih => exact ih.2.withoutDeclarations
  | executionGroup _ ih => exact ih.2.withoutDeclarations
  | item _ entry ih =>
      exact (ih.member (List.mem_of_getElem? entry)).1.withoutDeclarations

/-- An item-list lower bound covers each selected child's scopes.
Witness: membership induction through the item-list certificate.
-/
theorem ItemsUnder.member {base items} (under : ItemsUnder base items)
    {result children} (member : (result, children) ∈ items)
    : ScopesUnder base children := by
  induction items with
  | nil => cases member
  | cons entry rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst entry
        exact under.1
      · exact ih under.2 later

/-- A lower scope bound is retained by every located subtree.
Witness: each node inventory and item-list clause uses the same enclosing base.
-/
theorem ScopesUnder.located {base work address current producer enclosing}
    (under : ScopesUnder base work)
    (located : Located work address current producer enclosing)
    : ScopesUnder base current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact under.withoutDeclarations
  | left _ ih => exact ih.1.withoutDeclarations
  | right _ ih => exact ih.2.withoutDeclarations
  | executionGroup _ ih => exact ih.2.withoutDeclarations
  | item _ entry ih =>
      exact (ih.2.member (List.mem_of_getElem? entry)).withoutDeclarations

/-- Every represented node scope lies below a certified lower bound.
Witness: its group inventory entry or its stream boundary at the located subtree.
-/
theorem ScopesUnder.node {base work node kind dependencies producer}
    (under : ScopesUnder base work) (known : NodeAt work node kind dependencies producer)
    : base.IsPrefix node.path := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have localScopes := under.located located.toCurrent
      exact localScopes.1 _
        (List.mem_flatMap.mpr ⟨_, member, by simp [OwnerPaths.fragmentNodes]⟩)
  | stream located => exact (under.located located.toCurrent).1

/-- A known defer dependency's notice scope covers the dependent group's notice scope.
Witness: the group's actual ancestor descriptor and stable ref-to-path metadata.
-/
theorem WorkScoped.dependency_prefix
    {work paths bound node dependencies producer ancestor kind parents birth}
    (certified : WorkScoped work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (known : NodeAt work node .group dependencies producer)
    (parent : NodeAt work ancestor kind parents birth)
    (member : ancestor.ref ∈ dependencies)
    : ancestor.path.IsPrefix node.path := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | @group address groups path result children producer owners group located inGroups =>
      obtain ⟨entry, included, same⟩ := List.mem_map.mp member
      have scopedFragment := (certified.located located.toCurrent).1 group inGroups
      have localWork := workAt_located coherent located.toCurrent
      rw [MixedOwnerPaths.WorkAt] at localWork
      have assigned := localWork.1
      have entryKnown := (assigned entry (List.mem_flatMap.mpr
        ⟨group, inGroups, by simp [OwnerPaths.fragmentNodes, included]⟩)).1
      have ancestorKnown := workAt_node coherent parent
      have samePath : entry.path = ancestor.path :=
        entryKnown.2.symm.trans (same ▸ ancestorKnown.2)
      exact samePath ▸ scopedFragment _ included

/-- Producer context distinguishes defer continuity from fresh stream-item scopes.
Witness: navigation induction through the generating edge, retaining the stream's actual
node and result when its item is the producer.
-/
theorem producer_scope_context
    {parents bound work address current enclosing producer}
    (coherent : MixedRefs.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (certified : WorkScoped work)
    (located : Located work address current (some producer) enclosing)
    : ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ match (generalizing := false) producer with
          | .executionGroup _ =>
              DeferUnder parents owners current ∧ OwnersBefore owners current
          | .item _ _ =>
              ∃ node result,
                owners = [node.ref]
                ∧ payload = .item node result
                ∧ MixedRefs.WorkAt parents (node.ref + 1) bound current
                ∧ ScopesUnder node.path current := by
  have context {address current birth enclosing}
      (navigation : StructuralEquivalence.Located work address current birth enclosing)
      {producer} (generated : birth = some producer) :
      ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ match (generalizing := false) producer with
          | .executionGroup _ =>
              DeferUnder parents owners current ∧ OwnersBefore owners current
          | .item _ _ =>
              ∃ node result,
                owners = [node.ref] ∧ payload = .item node result
                ∧ MixedRefs.WorkAt parents (node.ref + 1) bound current
                ∧ ScopesUnder node.path current := by
    induction navigation with
    | root => contradiction
    | left _ ih =>
        obtain ⟨owners, ancestor, payload, task, support⟩ := ih generated
        refine ⟨owners, ancestor, payload, task, ?_⟩
        cases producer with
        | executionGroup address =>
            exact ⟨support.1.1.withoutDeclarations, support.2.1.withoutDeclarations⟩
        | item address index =>
            obtain ⟨node, result, owners, payload, refs, scopes⟩ := support
            rw [MixedRefs.WorkAt] at refs
            exact ⟨node, result, owners, payload, coherent_withoutDeclarations refs.1, scopes.1.withoutDeclarations⟩
    | right _ ih =>
        obtain ⟨owners, ancestor, payload, task, support⟩ := ih generated
        refine ⟨owners, ancestor, payload, task, ?_⟩
        cases producer with
        | executionGroup address =>
            exact ⟨support.1.2.withoutDeclarations, support.2.2.withoutDeclarations⟩
        | item address index =>
            obtain ⟨node, result, owners, payload, refs, scopes⟩ := support
            rw [MixedRefs.WorkAt] at refs
            exact ⟨node, result, owners, payload, coherent_withoutDeclarations refs.2, scopes.2.withoutDeclarations⟩
    | executionGroup navigation =>
        cases generated
        have properties := dependencyProperties_located continuous ordered navigation.toCurrent
        simp only [DeferContinuous, StreamOwnersOrdered] at properties
        exact ⟨_, _, _, TaskAt.executionGroup navigation.toCurrent,
          properties.1.1.withoutDeclarations, properties.2.1.withoutDeclarations⟩
    | item navigation selected =>
        cases generated
        have localRefs := coherent_located coherent navigation.toCurrent
        rw [MixedRefs.WorkAt] at localRefs
        have localScopes := certified.located navigation.toCurrent
        exact ⟨_, _, _, TaskAt.item navigation.toCurrent selected, _, _, rfl, rfl,
          coherent_withoutDeclarations (localRefs.2.2 _ (List.mem_of_getElem? selected)),
          (localScopes.member (List.mem_of_getElem? selected)).2.withoutDeclarations⟩
  exact context (StructuralEquivalence.located_of_current located) rfl

/-- A contributing owner's notice scope covers its task's data attachment.
Witness: the coherent owner-map prefix, expressed using the common payload path.
-/
theorem owner_payload_prefix
    {paths bound work occurrence owners producer payload node kind dependencies birth}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (known : TaskAt work occurrence owners producer payload)
    (owner : NodeAt work node kind dependencies birth) (member : node.ref ∈ owners)
    : node.path.IsPrefix payload.path := by
  obtain ⟨suffix, equal⟩ := workAt_owner_prefix coherent known owner member
  cases payload <;> exact ⟨suffix, equal.symm⟩

/-- A child task has a no-larger producer owner whose notice scope covers the child owner
scope. Witness: reused/ancestral defer support, fresh stream-item scope bounds, or the
ordinary producer attachment for a streamed child. This concerns notice scopes, not the
stronger and false claim that each producer payload covers the child notice scope.
-/
theorem producer_owner_scope
    {ancestry refBound paths pathBound base work occurrence owners producer payload
      node kind dependencies birth}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work) (certified : WorkScoped work)
    (known : TaskAt work occurrence owners (some producer) payload)
    (descriptor : NodeAt work node kind dependencies birth) (member : node.ref ∈ owners)
    : ∃ parentOwners ancestor result parent parentKind parents,
        TaskAt work producer parentOwners ancestor result
        ∧ NodeAt work parent parentKind parents ancestor
        ∧ parent.ref ∈ parentOwners
        ∧ parent.ref ≤ node.ref
        ∧ parent.path.IsPrefix node.path := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨group, inGroups, sameRef⟩ := List.mem_map.mp member
      have groupKnown := NodeAt.group located.toCurrent inGroups
      have samePath := workAt_same_path pathCoherent groupKnown descriptor sameRef
      obtain ⟨parentOwners, ancestor, result, parentTask, support⟩ :=
        producer_scope_context coherent continuous ordered certified located.toCurrent
      cases producer with
      | executionGroup address =>
          obtain ⟨ref, contributes, reused | ancestorRef⟩ := support.1.1 group inGroups
          · obtain ⟨parent, parentKind, parents, parentKnown, parentRef⟩ :=
              parentTask.owner_at_producer contributes
            refine ⟨_, _, _, parent, parentKind, parents, parentTask, parentKnown,
              parentRef.symm ▸ contributes, Nat.le_of_eq (parentRef.trans reused |>.trans
                sameRef), ?_⟩
            have equal := workAt_same_path pathCoherent parentKnown groupKnown
              (parentRef.trans reused)
            rw [equal, samePath]
            exact ⟨[], by simp⟩
          · obtain ⟨parent, parentKind, parents, parentKnown, parentRef⟩ :=
              parentTask.owner_at_producer contributes
            have bounds := coherent_node_bounds coherent groupKnown
            have earlier := (valid group.node.ref bounds.2 ref ancestorRef).1
            have canonical := DeferOnly.node_dependencies coherent groupKnown
            have inDependencies : parent.ref ∈ group.ancestors.map DeliveryNode.ref := by
              rw [canonical, parentRef]
              exact ancestorRef
            refine ⟨_, _, _, parent, parentKind, parents, parentTask, parentKnown,
              parentRef.symm ▸ contributes, ?_, ?_⟩
            · rw [parentRef, ← sameRef]
              exact Nat.le_of_lt earlier
            · rw [← samePath]
              exact certified.dependency_prefix pathCoherent groupKnown parentKnown
                inDependencies
      | item address index =>
          obtain ⟨stream, itemResult, ownersEq, payloadEq, refs, scopes⟩ := support
          obtain ⟨parent, parentKind, parents, parentKnown, parentRef⟩ :=
            parentTask.owner_at_producer (ownersEq.symm ▸ (by simp : stream.ref ∈ [stream.ref]))
          rw [MixedRefs.WorkAt] at refs
          refine ⟨
            _,
            _,
            _,
            parent,
            parentKind,
            parents,
            parentTask,
            parentKnown,
            parentRef.symm ▸ (ownersEq.symm ▸ (by simp : stream.ref ∈ [stream.ref])),
            ?_,
            ?_
          ⟩
          · rw [parentRef, ← sameRef]
            exact Nat.le_trans (Nat.le_succ _) (refs.2.1 group inGroups).1
          · have lower := owner_payload_prefix pathCoherent parentTask parentKnown
              (parentRef.symm ▸ (ownersEq.symm ▸ (by simp : stream.ref ∈ [stream.ref])))
            rw [payloadEq, Payload.path] at lower
            have scopedPath : stream.path.IsPrefix group.node.path := scopes.1 _
              (List.mem_flatMap.mpr ⟨group, inGroups, by simp [OwnerPaths.fragmentNodes]⟩)
            exact samePath ▸ lower.trans scopedPath
  | item located entry =>
      have actualKnown := NodeAt.stream located.toCurrent
      have sameRef : _ = node.ref := (List.mem_singleton.mp member).symm
      have samePath := workAt_same_path pathCoherent actualKnown descriptor sameRef
      obtain ⟨parentOwners, ancestor, result, parentTask, support⟩ :=
        producer_scope_context coherent continuous ordered certified located.toCurrent
      cases producer with
      | executionGroup address =>
          obtain ⟨ref, contributes⟩ := List.exists_mem_of_ne_nil _
            (coherent_task_owners_nonempty coherent parentTask)
          obtain ⟨parent, parentKind, parents, parentKnown, parentRef⟩ :=
            parentTask.owner_at_producer contributes
          refine ⟨_, _, _, parent, parentKind, parents, parentTask, parentKnown,
            parentRef.symm ▸ contributes, ?_, ?_⟩
          · rw [parentRef, ← sameRef]
            exact Nat.le_of_lt (support.2 ref contributes)
          · have lower := owner_payload_prefix pathCoherent parentTask parentKnown
              (parentRef.symm ▸ contributes)
            have below := under.producer_prefix known parentTask
            simpa only [Payload.path, samePath] using lower.trans below
      | item address index =>
          obtain ⟨stream, itemResult, ownersEq, payloadEq, refs, scopes⟩ := support
          obtain ⟨parent, parentKind, parents, parentKnown, parentRef⟩ :=
            parentTask.owner_at_producer (ownersEq.symm ▸ (by simp : stream.ref ∈ [stream.ref]))
          rw [MixedRefs.WorkAt] at refs
          refine ⟨
            _,
            _,
            _,
            parent,
            parentKind,
            parents,
            parentTask,
            parentKnown,
            parentRef.symm ▸ (ownersEq.symm ▸ (by simp : stream.ref ∈ [stream.ref])),
            ?_,
            ?_
          ⟩
          · rw [parentRef, ← sameRef]
            exact Nat.le_trans (Nat.le_succ _) refs.1
          · have lower := owner_payload_prefix pathCoherent parentTask parentKnown
              (parentRef.symm ▸ (ownersEq.symm ▸ (by simp : stream.ref ∈ [stream.ref])))
            rw [payloadEq, Payload.path] at lower
            exact samePath ▸ lower.trans scopes.1

end GraphQL.IncrementalDelivery.Correctness.ScopeMetadata
