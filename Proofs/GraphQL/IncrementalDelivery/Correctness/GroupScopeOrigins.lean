import Proofs.GraphQL.IncrementalDelivery.Correctness.ScopeProvenance
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.GroupAccounting
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedRefRoles
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedMixedOwners

/-! Each group has a root origin or an earlier producer owner covering its notice scope. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling WorkQueueSemantics

/-- A group ref has a root descriptor or an introducing task with an earlier contributing
owner whose notice scope covers the group scope. The producer's payload may be narrower.
This certificate contains no outputs, notices, failures, cancellations, or report premise.
-/
def GroupScopeOrigin (work : Work) (ref : NodeRef) : Prop :=
  ∃ origin dependencies producer,
    NodeAt work origin .group dependencies producer
    ∧ origin.ref = ref
    ∧ (producer = none
        ∨ ∃ source owners ancestor payload parent kind parents,
            producer = some source
            ∧ TaskAt work source owners ancestor payload
            ∧ NodeAt work parent kind parents ancestor
            ∧ parent.ref ∈ owners
            ∧ parent.ref < origin.ref
            ∧ parent.path.IsPrefix origin.path)

/-- Every represented group ref has a root or earlier scope-covering producer owner. -/
def GroupScopeOrigins (work : Work) : Prop :=
  ∀ node dependencies producer,
    NodeAt work node .group dependencies producer → GroupScopeOrigin work node.ref

-----------------------------------------------------------------------------------------
-- Equal-ref reuse is discharged by structural rank, not a strict ref assumption
-----------------------------------------------------------------------------------------

/-- A contributing group has a scope origin on coherent scope-preserving work.
Witness: follow no-larger producer owners. A strictly earlier owner supplies the origin;
an equal group ref recurses at a smaller structural dependency rank. Stream/group role
separation rules out equal-ref stream producers. Task attachments need not cover scopes.
-/
theorem group_scope_origin_at_task
    {ancestry refBound roles paths pathBound base work address owners producer payload
      node dependencies birth}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (certified : ScopeMetadata.WorkScoped work)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (descriptor : NodeAt work node .group dependencies birth) (member : node.ref ∈ owners)
    : GroupScopeOrigin work node.ref := by
  have find : ∀ rank, ∀ address owners producer payload node dependencies birth,
      (.executionGroup address : Occurrence).dependencyRank = rank
      → TaskAt work (.executionGroup address) owners producer payload
      → NodeAt work node .group dependencies birth
      → node.ref ∈ owners
      → GroupScopeOrigin work node.ref := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
        intro address owners producer payload node dependencies birth rankEq task nodeKnown
          contributes
        obtain ⟨actual, parents, actualKnown, actualRef⟩ :=
          task.executionGroup_owner contributes
        have samePath := workAt_same_path pathCoherent actualKnown nodeKnown actualRef
        cases producer with
        | none => exact ⟨actual, parents, none, actualKnown, actualRef, Or.inl rfl⟩
        | some source =>
            obtain ⟨parentOwners, ancestor, parentPayload, parent, parentKind, parentDeps,
              parentTask, parentKnown, parentMember, noLarger, below⟩ :=
              ScopeMetadata.producer_owner_scope valid coherent continuous ordered
                pathCoherent under certified task nodeKnown contributes
            by_cases earlier : parent.ref < node.ref
            · refine ⟨actual, parents, some source, actualKnown, actualRef, Or.inr ?_⟩
              exact ⟨source, parentOwners, ancestor, parentPayload, parent, parentKind,
                parentDeps, rfl, parentTask, parentKnown, parentMember,
                actualRef.symm ▸ earlier, samePath.symm ▸ below⟩
            · have equal : parent.ref = node.ref := Nat.le_antisymm noLarger
                (Nat.le_of_not_lt earlier)
              have before := task.producer_dependency
              cases source with
              | executionGroup parentAddress =>
                  obtain ⟨parentGroup, dependencies, parentGroupKnown, sameRef⟩ :=
                    parentTask.executionGroup_owner parentMember
                  have origin := ih (Occurrence.executionGroup parentAddress).dependencyRank
                    (by simpa only [rankEq] using before.1) parentAddress parentOwners
                    ancestor parentPayload parentGroup dependencies ancestor rfl parentTask
                    parentGroupKnown (sameRef.symm ▸ parentMember)
                  exact (sameRef.trans equal) ▸ origin
              | item parentAddress index =>
                  cases StructuralEquivalence.taskAt_of_current parentTask with
                  | item located entry =>
                      have parentStream := NodeAt.stream located.toCurrent
                      have singleton := List.mem_singleton.mp parentMember
                      exact False.elim (stream_group_refs_distinct roleCoherent parentStream
                        nodeKnown (singleton.symm.trans equal))
  exact find _ address owners producer payload node dependencies birth rfl known
    descriptor member

/-- Coherent generated scope metadata supplies every group origin without an extra law.
Witness: each group descriptor gives a contributing task, then equal-ref producer descent.
-/
theorem groupScopeOrigins_of_scopes {ancestry refBound roles paths pathBound base work}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (certified : ScopeMetadata.WorkScoped work)
    : GroupScopeOrigins work := by
  intro node dependencies producer known
  obtain ⟨address, groups, path, result, children, enclosing, group, located, member,
    nodeEq, _⟩ := known
  exact group_scope_origin_at_task valid coherent roleCoherent continuous ordered
    pathCoherent under certified (TaskAt.executionGroup located)
    (nodeEq.symm ▸ NodeAt.group located member)
    (nodeEq ▸ List.mem_map.mpr ⟨group, member, rfl⟩)

/-- Every root execution supplies scope-covering group origins without a caller premise.
Witness: execution-derived ancestry, roles, path assignments, attachment locality, and
scope metadata instantiate the structural-rank origin theorem. This includes shared refs,
produced defer groups, stream-item groups, errors, and exhausted fuel.
-/
theorem executeRoot_groupScopeOrigins (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : GroupScopeOrigins
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          0).1.work := by
  obtain ⟨_, ancestry, valid, coherent, continuous⟩ :=
    executeRoot_continuity schema resolvers variables fuel parentType source selections 0
  obtain ⟨roles, roleCoherent⟩ := RefRoles.executeRoot_roles schema resolvers variables fuel
    parentType source selections 0
  obtain ⟨paths, pathCoherent⟩ := MixedOwnerPaths.executeRoot_owners schema resolvers variables
    fuel parentType source selections 0
  exact groupScopeOrigins_of_scopes valid coherent roleCoherent continuous
    (executeRoot_streamOwnersOrdered schema resolvers variables fuel parentType source selections 0)
    pathCoherent
    (ExecutionPaths.executeRootSelectionSetCore_under schema resolvers variables fuel
      parentType source selections 0)
    (ScopeMetadata.executeRootSelectionSetCore_scopes schema resolvers variables fuel
      parentType source selections 0).1

end GraphQL.IncrementalDelivery.Correctness
