import Proofs.GraphQL.IncrementalDelivery.Correctness.BoundedTaskReportAssembly
import Proofs.GraphQL.IncrementalDelivery.Correctness.AcceptedFailureReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.UnannouncedGroupFailureOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingClosures

/-! Structural group origins close the unavailable-producer reporting induction. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A structural certificate, independent of events and failure reporting
-----------------------------------------------------------------------------------------

/-- Each represented group ref has a root descriptor or an introducing producer whose
attachment covers its scope and has an earlier contributing ref. Reused descriptors may
have narrower producers; only one suitable origin is required. This proof-only certificate
contains no output history, notice, cancellation, error count, or reporting obligation.
It is sufficient for selected work shapes, but stronger than arbitrary root execution:
ScopeMetadata's generated regression refutes it. GroupScopeOrigins instead uses the
introducing owner's notice scope, which may be broader than its payload attachment.
-/
def GroupProducerOrigins (work : Work) : Prop :=
  ∀ node dependencies producer,
    NodeAt work node .group dependencies producer
    → ∃ origin parents birth,
        NodeAt work origin .group parents birth
        ∧ origin.ref = node.ref
        ∧ (birth = none
            ∨ ∃ source owners ancestor payload ref,
                birth = some source
                ∧ TaskAt work source owners ancestor payload
                ∧ ref ∈ owners
                ∧ ref < origin.ref
                ∧ payload.path.IsPrefix origin.path)

/-- Root group descriptors satisfy structural origins without an introducing task.
Witness: retain the supplied descriptor and choose the root alternative.
-/
theorem groupProducerOrigins_of_root_groups {work}
    (roots
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer → producer = none)
    : GroupProducerOrigins work := by
  intro node dependencies producer known
  exact ⟨node, dependencies, producer, known, rfl, Or.inl (roots _ _ _ known)⟩

-----------------------------------------------------------------------------------------
-- Earlier task-local scopes report an unavailable introducing producer
-----------------------------------------------------------------------------------------

/-- A failed contributing group reports its task using only earlier failed-owner scopes.
Witness: descend through failed defer ancestors, choosing a structural origin at each ref.
An announced origin gives its actual positive scope. An unpublished introducing producer
is cancelled by accounting and covered by bounded causal assembly at an earlier ref;
the origin attachment prefix then reaches the task's own defer-map attachment.
No desired report is included in the structural origin certificate.
-/
theorem Explains.failed_owner_reported_of_earlier_scopes
    {ancestry refBound roles base paths pathBound work groups streams events matching
      failures address owners producer payload owner dependencies birth}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (origins : GroupProducerOrigins work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : GroupNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (satisfied
      : ∀ ref,
          ¬NodeFailed work matching events failures ref
          → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
              events failures ref)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (earlierReports
      : ∀ address owners producer payload node dependencies birth,
          TaskAt work (.executionGroup address) owners producer payload
          → NodeAt work node .group dependencies birth
          → node.ref ∈ owners
          → node.ref < owner.ref
          → NodeFailed work matching events failures node.ref
          → FailureReportedFor events payload.path)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ownerKnown : NodeAt work owner .group dependencies birth)
    (contributes : owner.ref ∈ owners)
    (failed : NodeFailed work matching events failures owner.ref)
    : FailureReportedFor events payload.path := by
  have canonical : ∀ node dependencies producer,
      NodeAt work node .group dependencies producer → dependencies = ancestry node.ref :=
    fun _ _ _ known => DeferOnly.node_dependencies coherent known
  have descend : ∀ ref, ∀ node parents source,
      NodeAt work node .group parents source
      → node.ref = ref
      → (ref = owner.ref ∨ ref ∈ dependencies)
      → NodeFailed work matching events failures ref
      → FailureReportedFor events payload.path := by
    intro ref
    induction ref using Nat.strongRecOn with
    | ind ref ih =>
        intro node parents source descriptor same related failed
        obtain ⟨origin, originParents, originBirth, originKnown, sameOrigin, support⟩ :=
          origins _ _ _ descriptor
        have originRef : origin.ref = ref := sameOrigin.trans same
        have originFailed : NodeFailed work matching events failures origin.ref :=
          originRef ▸ failed
        have transport : FailureReportedFor events origin.path
            → FailureReportedFor events payload.path := by
          intro report
          rcases related with direct | ancestor
          · have path := workAt_same_path pathCoherent originKnown ownerKnown
              (originRef.trans direct)
            rw [path] at report
            exact reported_owner_covers_task pathCoherent known ownerKnown contributes report
          · exact reported_owner_ancestor_covers_task pathCoherent canonical known ownerKnown
              contributes originKnown (originRef.symm ▸ ancestor) report
        by_cases announced
          : origin.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
        · exact transport (Explains.announced_failed_group_reports_scope valid coherent
            roleCoherent pathCoherent positive explained closedRefs originKnown announced
            originFailed)
        · rcases Explains.unannounced_group_failure_origin coherent roleCoherent explained
            covered satisfied originKnown announced originFailed with ancestor | unavailable
          · obtain ⟨parent, member, failedParent⟩ := ancestor
            have full := canonical _ _ _ originKnown
            have bounded := (coherent_node_bounds coherent originKnown).2
            have prior := valid origin.ref bounded parent (full ▸ member)
            obtain ⟨ancestor, kind, dependencies', birth', known', parentRef⟩ :=
              Explains.failed_node_known explained failedParent
            have group : kind = .group := by
              have role := node_ref_role roleCoherent known'
              have parentRole := group_dependency_role roleCoherent originKnown member
              rw [parentRef, parentRole] at role
              cases kind with
              | group => rfl
              | stream => cases role
            subst kind
            apply ih parent (by simpa only [originRef] using prior.1) ancestor
              dependencies' birth' known' parentRef ?_ failedParent
            right
            rcases related with direct | above
            · have original := canonical _ _ _ ownerKnown
              simpa only [full, originRef, direct, original] using member
            · have original := canonical _ _ _ ownerKnown
              have higher := valid owner.ref (coherent_node_bounds coherent ownerKnown).2
                ref (original ▸ above)
              have parentMember : parent ∈ ancestry origin.ref := full ▸ member
              rw [original]
              exact higher.2 (by simpa only [originRef] using parentMember)
          · obtain ⟨source, generated, unpublished⟩ := unavailable
            rcases support with root | introduced
            · cases root.symm.trans generated
            · obtain ⟨parent, parentOwners, parentBirth, parentPayload, parentRef,
                parentEq, parentKnown, member, before, below⟩ := introduced
              cases Option.some.inj (parentEq.symm.trans generated)
              have upper : origin.ref ≤ owner.ref := by
                rcases related with direct | ancestor
                · exact Nat.le_of_eq (originRef.trans direct)
                · have full := canonical _ _ _ ownerKnown
                  have prior := valid owner.ref (coherent_node_bounds coherent ownerKnown).2
                    ref (full ▸ ancestor)
                  exact Nat.le_of_lt (by simpa only [originRef] using prior.1)
              have cancelled := (accounted _ _ _ _ parentKnown).resolve_right unpublished
              have reported := cancelled_reported_of_bounded_owner_task_scopes valid
                coherent roleCoherent continuous ordered pathCoherent under earlierReports
                (fun cut task recorded owners birth result descriptor =>
                  Explains.accepted_failure_reported valid coherent roleCoherent pathCoherent
                    positive explained closedRefs recorded descriptor)
                cancelled parentKnown member (Nat.lt_of_lt_of_le before upper)
              exact transport (reported.descendant below)
  exact descend owner.ref owner dependencies birth ownerKnown rfl (Or.inl rfl) failed

-----------------------------------------------------------------------------------------
-- Strong ref induction supplies all the earlier scopes instead of assuming them globally
-----------------------------------------------------------------------------------------

/-- Every failed defer owner covers its contributing task at an accounted closed frontier.
Witness: strong induction on the owner ref using structural group origins and the bounded
producer step. All earlier task-local scopes are constructed recursively. The only report
origins are actual announced failures and accepted settlements, not an assumed terminal law.
-/
theorem Explains.failed_owner_reported_of_group_origins
    {ancestry refBound roles base paths pathBound work groups streams events matching
      failures address owners producer payload owner dependencies birth}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (origins : GroupProducerOrigins work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : GroupNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (satisfied
      : ∀ ref,
          ¬NodeFailed work matching events failures ref
          → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
              events failures ref)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ownerKnown : NodeAt work owner .group dependencies birth)
    (contributes : owner.ref ∈ owners)
    (failed : NodeFailed work matching events failures owner.ref)
    : FailureReportedFor events payload.path := by
  have all : ∀ ref, ∀ address owners producer payload owner dependencies birth,
      owner.ref = ref
      → TaskAt work (.executionGroup address) owners producer payload
      → NodeAt work owner .group dependencies birth
      → owner.ref ∈ owners
      → NodeFailed work matching events failures owner.ref
      → FailureReportedFor events payload.path := by
    intro ref
    induction ref using Nat.strongRecOn with
    | ind ref ih =>
        intro address owners producer payload owner dependencies birth same known descriptor
          member failed
        apply Explains.failed_owner_reported_of_earlier_scopes valid coherent roleCoherent
          continuous ordered pathCoherent under positive origins explained covered
          satisfied closedRefs accounted ?_ known descriptor member failed
        intro address owners producer payload node dependencies birth task known member
          before failed
        exact ih node.ref (by simpa only [same] using before) address owners producer
          payload node dependencies birth rfl task known member failed
  exact all owner.ref address owners producer payload owner dependencies birth rfl known
    ownerKnown contributes failed

/-- Accounted cancellation is reported when structural group origins are certified.
Witness: strong-ref failed-owner reporting supplies the task-local origins; accepted
failure reporting and mutual causal assembly cover streams and structural producers.
The structural certificate is still required and is not inferred from admission alone.
-/
theorem Explains.cancelled_reported_of_group_origins
    {ancestry refBound roles base paths pathBound work groups streams events matching
      failures occurrence owners producer payload}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (origins : GroupProducerOrigins work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : GroupNoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
          events failures)
    (satisfied
      : ∀ ref,
          ¬NodeFailed work matching events failures ref
          → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching
              events failures ref)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  apply cancelled_reported_of_owner_task_scopes roleCoherent pathCoherent under ?_ ?_
    cancelled known
  · intro address owners producer payload node dependencies birth task descriptor member
      failed
    exact Explains.failed_owner_reported_of_group_origins valid coherent roleCoherent
      continuous ordered pathCoherent under positive origins explained covered satisfied
      closedRefs accounted task descriptor member failed
  · intro cut task recorded owners birth result descriptor
    exact Explains.accepted_failure_reported valid coherent roleCoherent pathCoherent positive
      explained closedRefs recorded descriptor

-----------------------------------------------------------------------------------------
-- Complete reporting histories reduce to structural execution provenance
-----------------------------------------------------------------------------------------

/-- A reporting-covered prefix with structural group origins has a complete continuation.
Witness: reach a closed accounted reporting frontier, construct every actual cancellation
scope by ref induction, then finish while retaining the supplied batches. This conditional
helper does not apply to every root execution; its producer-payload premise is stronger
than the execution-derived owner-scope certificate in GroupScopeOrigins.
-/
theorem mixed_reporting_continuation_of_group_origins
    {ancestry refBound roles base paths pathBound work groups streams events matching
      failures batches}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (origins : GroupProducerOrigins work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (batched : WorkBatching events batches)
    : (History.mk groups streams batches).CanFinish work := by
  obtain ⟨tail, next, cuts, extended, frontier, accounted, closed, satisfied⟩ :=
    mixed_reporting_closed_extension valid coherent roleCoherent continuous ordered
      pathCoherent explained covered
  have reports : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload
      → ¬Published next (events ++ tail) occurrence
      → FailureReportedFor (events ++ tail) payload.path := by
    intro occurrence owners producer payload known unpublished
    exact Explains.cancelled_reported_of_group_origins valid coherent roleCoherent continuous
      ordered pathCoherent under positive origins extended frontier.2 satisfied closed
      accounted ((accounted _ _ _ _ known).resolve_right unpublished) known
  obtain ⟨closures, run, _, _⟩ :=
    (batched.append (WorkBatching.singletons tail)).finish_accounted extended accounted reports
  refine ⟨tail.map (fun event => [event]) ++ closures.map (fun event => [event])
    ++ [[.workQueueTermination]], ?_⟩
  simpa only [List.append_assoc] using run

/-- Certified nonempty mixed work admits a complete finite reporting run.
Witness: covering initialization and the structural-origin continuation. This admits
produced defer groups and nested streams, but does not assume an output schedule or
terminal report. Arbitrary root execution instead supplies the weaker owner-scope origins;
the general reporting proof must use those rather than this stronger sufficient condition.
-/
theorem mixed_completeRun_exists_of_group_origins
    {ancestry refBound roles base paths pathBound work}
    (valid : Valid ancestry refBound)
    (coherent : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (origins : GroupProducerOrigins work)
    (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history := by
  obtain ⟨groups, streams, initialized⟩ :=
    initialization_exists valid coherent continuous ordered nonempty
  obtain ⟨groups, streams, initialized, covers⟩ := initialized.covering_exists
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  obtain ⟨batches, run⟩ := mixed_reporting_continuation_of_group_origins valid coherent
    roleCoherent continuous ordered pathCoherent under positive origins initial
    (reportingNoticesCovered_of_noticesCovered (NoticesCovered.initial covers _))
    WorkBatching.nil
  exact ⟨⟨groups, streams, batches⟩, run⟩

end GraphQL.IncrementalDelivery.Correctness
