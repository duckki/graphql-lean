import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExposedRegions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectProducerSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordFailureRoles
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay

/-! Mixed group failure reduces to cleanup once exposed stream-item producers are safe. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open Semantics.RefRoles

-----------------------------------------------------------------------------------------
-- Generated roles and exposed ancestry supply the local induction certificates
-----------------------------------------------------------------------------------------

/-- Structural descriptors retain the root's defer/stream role assignment.
Witness: project the located contributor or stream's metadata.
-/
private theorem node_role {work roles node kind dependencies producer}
    (assigned : WorkRoles roles work)
    (known : NodeAt work node kind dependencies producer)
    : roles node.ref = (kind == .stream) := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have localWork := generatedWorkRoles_located assigned located
      simp only [WorkRoles] at localWork
      exact (localWork.1 _ member).1
  | stream located =>
      have localWork := generatedWorkRoles_located assigned located
      simp only [WorkRoles] at localWork
      exact localWork.1

/-- Every group dependency has defer role, even if it is a taskless ancestor.
Witness: the descriptor records its complete ancestor list in one located fragment.
-/
private theorem dependency_role {work roles node dependencies producer ref}
    (assigned : WorkRoles roles work)
    (known : NodeAt work node .group dependencies producer) (member : ref ∈ dependencies)
    : roles ref = false := by
  obtain ⟨address, groups, path, result, children, enclosing, fragment,
    located, included, _, same⟩ := known
  rw [same] at member
  obtain ⟨ancestor, ancestorMember, rfl⟩ := List.mem_map.mp member
  have localWork := generatedWorkRoles_located assigned
    (StructuralEquivalence.located_of_current located)
  simp only [WorkRoles] at localWork
  exact (localWork.1 fragment included).2 ancestor ancestorMember

/-- An exposed child's supporting object-producer owner is exposed too.
Witness: generated local defer continuity picks a reused ref or full ancestor; exposure
is shared across that region. This transfers invalidation without requiring publication.
-/
private theorem lift_objectProducer {work failed seen node dependencies source}
    (generated : ExecutedWork work)
    (known : NodeAt work node .group dependencies (some (.executionGroup source)))
    (exposed : ExposedRef work seen node.ref)
    (invalid
      : ∀ owners ancestor payload ref,
          TaskAt work (.executionGroup source) owners ancestor payload
          → ref ∈ owners
          → ExposedRef work seen ref
          → GroupInvalidated work failed ref)
    : GroupInvalidated work failed node.ref := by
  obtain ⟨owners, ancestor, payload, ref, task, member, support⟩ :=
    generated.group_objectProducer_support known
  have parentExposed : ExposedRef work seen ref := by
    apply NodeAt.group_exposedChain known generated.regionsSeparated exposed
    exact List.mem_cons.mpr support
  have failure := invalid owners ancestor payload ref task member parentExposed
  rcases support with same | dependency
  · exact same ▸ failure
  · exact .groupDependency ⟨node, _, known, rfl⟩ dependency failure

-----------------------------------------------------------------------------------------
-- The mutual causal induction stops only at genuinely safe item boundaries
-----------------------------------------------------------------------------------------

/-- Snapshot failure of an exposed generated group has a direct/ancestor cleanup cause.
Witness: mutual failure/cancellation induction. Object edges preserve defer support;
item edges name an observed region and stop at that item's failure/cancellation safety.
Unobserved or cancelled items elsewhere in the work tree need no safety certificate.
-/
theorem ExecutedWork.exposed_snapshotGroupFailure_invalidated
    {work failed published seen node dependencies producer}
    (generated : ExecutedWork work)
    (known : NodeAt work node .group dependencies producer)
    (exposed : ExposedRef work seen node.ref)
    (itemsNotFailed
      : ∀ source index,
          Occurrence.item source index ∈ seen → Occurrence.item source index ∉ failed)
    (itemsSafe
      : ∀ source index,
          Occurrence.item source index ∈ seen
          → ¬Causality.TaskCancelled work failed published (.item source index))
    (failure : Causality.NodeFailed work failed published node.ref)
    : GroupInvalidated work failed node.ref := by
  obtain ⟨roles, assigned⟩ := generated.refRoles
  have reflect {ref} (cause : Causality.NodeFailed work failed published ref)
      : roles ref = false → ExposedRef work seen ref → GroupInvalidated work failed ref := by
    induction cause
      using Causality.NodeFailed.rec
        (motive_2 :=
          fun occurrence _ =>
            ∀ address owners producer payload ref,
              occurrence = .executionGroup address
              → TaskAt work occurrence owners producer payload
              → ref ∈ owners
              → ExposedRef work seen ref
              → GroupInvalidated work failed ref) with
    | task task owner member => exact fun _ _ => .task task owner member
    | groupDependency projected member _ ih =>
        intro _ exposed
        obtain ⟨group, birth, descriptor, same⟩ := projected
        exact .groupDependency ⟨group, birth, descriptor, same⟩ member
          (ih (dependency_role assigned descriptor member)
            (NodeAt.group_exposedChain descriptor generated.regionsSeparated
              (same.symm ▸ exposed) _ (List.mem_cons_of_mem _ member)))
    | streamDependencies projected _ _ _ =>
        intro role _
        obtain ⟨stream, birth, descriptor, same⟩ := projected
        have streamRole := node_role assigned descriptor
        rw [same, role] at streamRole
        cases streamRole
    | producers projected noRoot _ cancelled ih =>
        intro role exposed
        obtain ⟨birth, group, kind, dependencies, descriptor, same⟩ := projected
        have groupKind : kind = .group := by
          have actual := node_role assigned descriptor
          rw [same, role] at actual
          cases kind with
          | group => rfl
          | stream => cases actual
        subst kind
        have localExposure := same.symm ▸ exposed
        cases birth with
        | none =>
            exact False.elim (noRoot ⟨group, .group, dependencies, descriptor, same⟩)
        | some parent =>
            cases parent with
            | item source index =>
                have observed := NodeAt.group_itemProducer_seen descriptor
                  generated.regionsSeparated localExposure
                exact False.elim (itemsSafe source index observed
                  (cancelled _ ⟨group, .group, dependencies, descriptor, same⟩
                    (itemsNotFailed source index observed)))
            | executionGroup source =>
                apply same ▸ lift_objectProducer generated descriptor localExposure
                intro owners ancestor payload ref task member parentExposed
                by_cases recorded : Occurrence.executionGroup source ∈ failed
                · exact .task ⟨ancestor, payload, task⟩ member recorded
                · exact ih _ ⟨group, .group, dependencies, descriptor, same⟩ recorded
                    source owners ancestor payload ref rfl task member parentExposed
    | owners projected _ _ _ ih =>
        rename_i address owners producer payload ref same task member exposed
        cases same
        obtain ⟨birth, result, other⟩ := projected
        obtain ⟨group, dependencies, descriptor, refEq⟩ := TaskAt.executionGroup_owner task member
        exact ih ref ((task.unique other).1 ▸ member)
          (refEq ▸ node_role assigned descriptor) exposed
    | producerFailed projected unpublished recorded =>
        rename_i address owners producer payload ref same task member exposed
        cases same
        obtain ⟨otherOwners, result, other⟩ := projected
        have parentEq := (task.unique other).2.1
        subst producer
        obtain ⟨group, dependencies, descriptor, refEq⟩ := TaskAt.executionGroup_owner task member
        rename_i parent
        cases parent with
        | item source index =>
            have observed := NodeAt.group_itemProducer_seen descriptor generated.regionsSeparated
              (refEq.symm ▸ exposed)
            exact False.elim (itemsNotFailed source index observed recorded)
        | executionGroup source =>
            apply refEq ▸ lift_objectProducer generated descriptor (refEq.symm ▸ exposed)
            exact fun owners ancestor payload ref task member _ =>
              .task ⟨ancestor, payload, task⟩ member recorded
    | producerCancelled projected unpublished cancelled ih =>
        rename_i address owners producer payload ref same task member exposed
        cases same
        obtain ⟨otherOwners, result, other⟩ := projected
        have parentEq := (task.unique other).2.1
        subst producer
        obtain ⟨group, dependencies, descriptor, refEq⟩ := TaskAt.executionGroup_owner task member
        rename_i parent
        cases parent with
        | item source index =>
            exact False.elim (itemsSafe source index
              (NodeAt.group_itemProducer_seen descriptor generated.regionsSeparated
                (refEq.symm ▸ exposed)) cancelled)
        | executionGroup source =>
            apply refEq ▸ lift_objectProducer generated descriptor (refEq.symm ▸ exposed)
            exact fun owners ancestor payload ref task member parentExposed =>
              ih source owners ancestor payload ref rfl task member parentExposed
  exact reflect failure (node_role assigned known) exposed

/-- Historical group failure reduces to cleanup once successful source items are safe.
Witness: apply snapshot reflection at the original reached cut, retain item-safety
evidence at that cut, then enlarge only the failure inventory. Source matching proves
the exposing items successful, so genuine failure cuts cannot name those items.
This does not yet derive item safety or assume admitted output histories.
-/
theorem ExecutedWork.exposed_groupFailure_invalidated
    {work received matching events failures node dependencies producer}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (known : NodeAt work node .group dependencies producer)
    (exposed
      : ExposedRef work (received.flatMap (fun event => event.identities.1)) node.ref)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (itemsSafe
      : ∀ source index,
          Occurrence.item source index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item source index))
    (failure : NodeFailed work matching events failures node.ref)
    : GroupInvalidated work (failedBefore failures events.length) node.ref := by
  obtain ⟨cut, member, reached, cause⟩ := failure
  have reflected := generated.exposed_snapshotGroupFailure_invalidated known exposed
    (fun source index observed => taskSucceeds_not_failedBefore
      (valid.successes_succeed (valid.itemIdentity_success observed)) failedPayloads)
    (fun source index observed cancelled =>
      itemsSafe source index (valid.itemIdentity_success observed)
        ⟨cut, member, reached, cancelled⟩)
    cause
  exact reflected.mono (failedBefore_subset failures reached)

/-- The actual replay guard implies historical group health once observed items are safe.
Witness: registration exposes the group region; mixed causal reflection reduces failure
to cleanup, role separation removes stream-item contributions, and proved guard reflection
rejects the remaining accepted object inventory. The cut inventory may contain stream
failures; `objectsRecorded` relates only its object causes to actual accepted settlements.
-/
theorem ExecutedWork.replayGraphEvents_groupHealthy_of_itemSafety
    {work received matching events failures node dependencies producer}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch received = true)
    (known : NodeAt work node .group dependencies producer)
    (registered
      : node.ref
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            received).registeredGroups)
    (guardHealthy
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          received).groupIsHealthy
          node.ref
        = true)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (objectsRecorded
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failedBefore failures events.length
          → occurrence
            ∈ (State.initialize (Work.fromExecution work)).objectFailureContributions
                received)
    (itemsSafe
      : ∀ source index,
          Occurrence.item source index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item source index))
    : ¬NodeFailed work matching events failures node.ref := by
  intro failure
  have exposed := (createWorkQueue_replay_regionInventory valid).registered_exposed registered
  have invalid := generated.exposed_groupFailure_invalidated valid known exposed failedPayloads
    itemsSafe failure
  have recorded := invalid.toRecordInvalidated.restrict_objectFailures generated
    (groupRecordAt_of_nodeAt known) objectsRecorded
  exact generated.replayGraphEvents_groupIsHealthy_recordUninvalidated received valid started
    guardHealthy recorded

/-- An uncancelled retired group remains historically healthy under the same item boundary.
Witness: replay's retired-record health replaces the live guard; permanent registration
still supplies exposure, and mixed causal reflection retains each original failure cut.
This covers supporting groups removed by successful completion, not cancelled retirements.
-/
theorem ExecutedWork.replayGraphEvents_retiredGroupHealthy_of_itemSafety
    {work received matching events failures node dependencies producer}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch received = true)
    (known : NodeAt work node .group dependencies producer)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          received).RetiredGroup
          node.ref)
    (uncancelled
      : node.ref
        ∉ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            received).cancelledGroups)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (objectsRecorded
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failedBefore failures events.length
          → occurrence
            ∈ (State.initialize (Work.fromExecution work)).objectFailureContributions
                received)
    (itemsSafe
      : ∀ source index,
          Occurrence.item source index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item source index))
    : ¬NodeFailed work matching events failures node.ref := by
  intro failure
  have exposed := (createWorkQueue_replay_regionInventory valid).registered_exposed retired.1
  have invalid := generated.exposed_groupFailure_invalidated valid known exposed failedPayloads
    itemsSafe failure
  have recorded := invalid.toRecordInvalidated.restrict_objectFailures generated
    (groupRecordAt_of_nodeAt known) objectsRecorded
  exact (generated.replayGraphEvents_retiredHealth received valid started).1
    node dependencies (groupRecordAt_of_nodeAt known) retired uncancelled recorded

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
