import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReportingAvailability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExposedGroupCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeFailureInventory

/-! Initial synchronous causes license cancellation independently of aggregate reporting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open Semantics.RefRegions

/-- A producer-free location stays inside the original root reference region. -/
theorem Located.rootRefs_of_noProducer {work address current producer owners ref}
    (located : Located work address current producer owners) (root : producer = none)
    (member : ref ∈ rootRefs current)
    : ref ∈ rootRefs work := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact rootRefs_withoutDeclarations_subset _ member
  | left _ ih =>
      exact ih root (List.mem_append_left _ (rootRefs_withoutDeclarations_subset _ member))
  | right _ ih =>
      exact ih root (List.mem_append_right _ (rootRefs_withoutDeclarations_subset _ member))
  | executionGroup => cases root
  | item => cases root

/-- Root task contributors are exposed before any notification is consumed. -/
theorem NodeAt.rootGroup_exposed {work node dependencies seen}
    (known : NodeAt work node .group dependencies none)
    : ExposedRef work seen node.ref := by
  obtain ⟨address, groups, path, result, children, enclosing, group, located, included,
    same, _⟩ := known
  subst node
  apply Or.inl
  apply Located.rootRefs_of_noProducer located rfl
  exact List.mem_append_left _ (List.mem_flatMap.mpr
    ⟨group, included, List.mem_cons_self⟩)

/-- An informative producer-free failure cannot already have been causally cancelled.
Root exposure reflects owner failure into group invalidation; producer rules contradict
its fixed producer-free descriptor. The argument does not assume output admission.
-/
theorem ExecutedWork.rootTask_uncancelled
    {work occurrence owners path result matching events cuts}
    (generated : ExecutedWork work)
    (known : TaskAt work occurrence owners none (.object path result))
    (informative : InformativeFailure work (cuts.map Prod.snd) occurrence)
    : ¬TaskCancelled work matching events cuts occurrence := by
  obtain ⟨otherOwners, ref, ⟨producer, payload, descriptor⟩, contributes, healthy⟩ :=
    informative
  have same := (descriptor.unique known).1
  have owner := same ▸ contributes
  obtain ⟨node, dependencies, group, identity⟩ := TaskAt.objectOwner_groupNode known owner
  rintro ⟨cut, member, bounded, cancelled⟩
  cases cancelled with
  | owners task _ _ failures =>
      obtain ⟨birth, value, located⟩ := task
      have sameOwners := (known.unique located).1
      have failure := failures ref (sameOwners ▸ owner)
      have invalid := generated.exposed_snapshotGroupFailure_invalidated group
        (NodeAt.rootGroup_exposed (seen := []) group)
        (by intro source index impossible; cases impossible)
        (by intro source index impossible; cases impossible)
        (identity.symm ▸ failure)
      have included : (failedBefore cuts cut).Subset (cuts.map Prod.snd) :=
        fun _ present => List.mem_map.mpr (by
          obtain ⟨entry, selected, same⟩ := List.mem_map.mp present
          exact ⟨entry, (List.mem_filter.mp selected).1, same⟩)
      exact healthy (identity ▸ invalid.mono included)
  | producerFailed task _ _ =>
      obtain ⟨otherOwners, payload, descriptor⟩ := task
      cases (known.unique descriptor).2.1
  | producerCancelled task _ _ =>
      obtain ⟨otherOwners, payload, descriptor⟩ := task
      cases (known.unique descriptor).2.1

/-- Select informative initial causal cuts from the independently available reporting cuts.
The selection is proof evidence; neither startup execution nor reporting totals change.
-/
noncomputable def InitialStartup.causalCuts (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs)
    : FailureCuts :=
  selectObjectFailureCuts work [] (startup.reportingCuts work initial)

/-- Initial causal selection retains only supplied reporting entries at the initial cut. -/
theorem InitialStartup.causalCuts_sublist (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs)
    : (startup.causalCuts work initial).Sublist (startup.reportingCuts work initial) :=
  selectObjectFailureCuts_sublist work [] _

/-- Every selected initial causal settlement precedes the first output atom. -/
theorem InitialStartup.causalCuts_zero {startup work initial entry}
    (member : entry ∈ InitialStartup.causalCuts startup work initial)
    : entry.1 = 0 := by
  have available := (startup.causalCuts_sublist work initial).subset member
  obtain ⟨occurrence, _, same⟩ := List.mem_map.mp available
  exact (congrArg Prod.fst same).symm

/-- All selected initial causes are reached at every output boundary. -/
theorem InitialStartup.failedBefore_causalCuts (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs) (cut : Nat)
    : failedBefore (startup.causalCuts work initial) cut
      = (startup.causalCuts work initial).map Prod.snd := by
  unfold failedBefore
  rw [List.filter_eq_self.mpr]
  intro entry member
  simp only [startup.causalCuts_zero member, Nat.zero_le, decide_true]

/-- Causal selection reuses the initial reporting entries without adding any occurrence. -/
theorem InitialStartup.causalCuts_available (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs)
    : CausalFailuresAvailable (startup.causalCuts work initial)
        (startup.reportingCuts work initial) :=
  .of_sublist (startup.causalCuts_sublist work initial)

/-- Initial causal selection preserves all group invalidation justified by reporting causes. -/
theorem InitialStartup.causalCuts_groupInvalidated (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs) (ref : NodeRef)
    : GroupInvalidated work (startup.reportingOccurrences work initial) ref
      ↔ GroupInvalidated work ((startup.causalCuts work initial).map Prod.snd) ref := by
  have selected := selectObjectFailureCuts_groupInvalidated work []
    (startup.reportingCuts work initial) ref
  simpa [InitialStartup.reportingCuts, InitialStartup.causalCuts, List.map_map,
    Function.comp_def] using selected

/-- Initial causal selection also preserves cleanup of taskless ancestor records. -/
theorem InitialStartup.causalCuts_groupRecordInvalidated (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs) (ref : NodeRef)
    : GroupRecordInvalidated work (startup.reportingOccurrences work initial) ref
      ↔ GroupRecordInvalidated work ((startup.causalCuts work initial).map Prod.snd)
          ref :=
  groupRecordInvalidated_congr (startup.causalCuts_groupInvalidated work initial) ref

/-- Every selected initial failure is licensed against its own earlier causal prefix. -/
theorem ExecutedWork.initialStartup_failureWitness {work startup initial}
    (generated : ExecutedWork work) (matched : InitialStartup.MatchesWork startup work)
    (matching : PublicationMatching) (events : List Execution.WorkQueueEvent)
    : FailureWitness work initial matching events (startup.causalCuts work initial) := by
  have reporting := InitialStartup.reportingWitness (initial := initial) matched events
  have selected := selectObjectFailureCuts_informative work []
    (startup.reportingCuts work initial)
  intro before cut occurrence after split
  have member : (cut, occurrence) ∈ startup.causalCuts work initial := by simp [split]
  have available := (startup.causalCuts_sublist work initial).subset member
  obtain ⟨prior, remaining, reportSplit⟩ := List.mem_iff_append.mp available
  have report := reporting prior cut occurrence remaining reportSplit
  have source : occurrence ∈ startup.reportingOccurrences work initial := by
    obtain ⟨other, included, same⟩ := List.mem_map.mp available
    have identity : other = occurrence := (Prod.mk.inj same).2
    exact identity ▸ included
  have supplied := (InitialStartup.mem_reportingOccurrences.mp source).1
  obtain ⟨⟨address, errors⟩, received, identity⟩ := List.mem_map.mp supplied
  dsimp only at identity
  subst address
  obtain ⟨owners, path, known⟩ := InitialStartup.matched_rootFailure matched received
  have informative : InformativeFailure work (before.map Prod.snd) occurrence := by
    change InformativeFailureCuts work [] (startup.causalCuts work initial) at selected
    rw [split] at selected
    simpa only [List.nil_append] using selected.atCut
  refine ⟨report.1, ?_, report.2.2.2, generated.rootTask_uncancelled known informative⟩
  intro earlier included
  have earlierMember : earlier ∈ startup.reportingCuts work initial :=
    (startup.causalCuts_sublist work initial).subset (by
      rw [split]
      exact List.mem_append_left _ included)
  obtain ⟨left, _, leftEq⟩ := List.mem_map.mp earlierMember
  obtain ⟨right, _, rightEq⟩ := List.mem_map.mp available
  have leftZero := congrArg Prod.fst leftEq
  have rightZero := congrArg Prod.fst rightEq
  dsimp only at leftZero rightZero
  omega

/-- Each initial aggregate's group has a licensed causal failure at the initial cut.
The causal selection preserves invalidation without using aggregate counts as causes.
-/
theorem ExecutedWork.initialStartup_reports_failed {work startup}
    (generated : ExecutedWork work) (matched : InitialStartup.MatchesWork startup work)
    (matching : PublicationMatching) (events : List Execution.WorkQueueEvent)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      ∀ failure ∈ initial.groupFailureEvents,
        NodeFailed work matching events (startup.causalCuts work refs)
          failure.group.ref := by
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  intro failure emitted
  have reported := generated.initialStartup_reportingCauses startup matched failure emitted
  rw [InitialStartup.failedBefore_reportingCuts] at reported
  have rawInvalid : GroupInvalidated work (startup.reportingOccurrences work refs)
      failure.group.ref := by
    obtain ⟨causes, nonempty, distinct, licensed, total⟩ := reported
    cases causes with
    | nil => exact False.elim (nonempty rfl)
    | cons cause rest =>
        obtain ⟨available, owners, producer, payload, known, contributes, _, _⟩ :=
          licensed cause.1 cause.2 List.mem_cons_self
        exact .task ⟨producer, payload, known⟩ contributes available
  have invalid := (startup.causalCuts_groupInvalidated work refs failure.group.ref).mp rawInvalid
  have nonempty : startup.causalCuts work refs ≠ [] := by
    intro empty
    rw [empty, List.map_nil] at invalid
    exact invalid.nonempty rfl
  have present : 0 ∈ (startup.causalCuts work refs).map Prod.fst := by
    cases selected : startup.causalCuts work refs with
    | nil => exact False.elim (nonempty selected)
    | cons entry rest =>
        have member : entry ∈ startup.causalCuts work refs := selected ▸ List.mem_cons_self
        exact List.mem_map.mpr ⟨entry, List.mem_cons_self, startup.causalCuts_zero member⟩
  refine ⟨0, present, Nat.zero_le _, ?_⟩
  rw [InitialStartup.failedBefore_causalCuts]
  exact invalid.toCausality _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
