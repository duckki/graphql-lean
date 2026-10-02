import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SupportedOwnerHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemLineageCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationAdmission
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Supported publications protect produced streams without assuming history admission. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerSupportedCausality
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def localSchema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [{ name := "users", outputType := .list (.nonNull (.named "User")) }]
          },
        .object
          {
            name := "User",
            fields := [{ name := "values", outputType := .list (.named "String") }]
          }
      ]
  }

private def localResolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ name _ _ =>
        if name = "users" then
          some (.list [.object "User" 1, .null])
        else
          some (.list [.scalar "x"]),
    resolve_argumentsEquivalent := by intros; rfl
  }

private def selections : List Selection :=
  [field "users" [field "values" [] [.stream]] [.stream]]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore localSchema localResolvers [] 30 "Query"
      (.object "Query" 0) selections).run
    0).1.work

private def outer : DeliveryNode := { key := 0, path := [.field "users"] }

private def child : DeliveryNode :=
  { key := 1, path := [.field "users", .index 0, .field "values"] }

private def parent : Occurrence := .item [0, 0, 1] 0
private def failedItem : Occurrence := .item [0, 0, 1] 1
private def childItem : Occurrence := .item [0, 0, 1, 0, 0, 0, 1] 0
private def value : ResponseValue := .object [("values", .list [])]

private def childEntries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (.scalar "x", 0), .empty)]

private def children : Execution.Work :=
  .combine (.combine (.combine .empty (.stream child childEntries)) .empty) .empty

private def entries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (value, 0), children), (.error 1, .empty)]

private def first : GraphEvent :=
  .streamItems outer [⟨parent, ⟨value, 0⟩, Work.fromExecution children [0, 0, 1, 0]⟩]

private def inputs : List (List GraphEvent) := [[first], [.streamFailure outer 1]]

private def atoms : List Execution.WorkQueueEvent :=
  ((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
    publicationAtoms

private def cuts : FailureCuts := [(1, failedItem)]

private def matching : PublicationMatching :=
  fun index => if index = 0 then parent else childItem

/-- Real execution creates a streamed object before a non-null item failure.
Witness: this fixture's definition is precisely that root execution.
-/
private theorem generated : ExecutedWork work :=
  ⟨Nat, localSchema, localResolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- The outer stream retains the successful object's children and the later error.
Witness: evaluate its structural address in the generated work.
-/
private theorem outer_located
    : Located work [0, 0, 1] (.stream outer entries) none [] := by cbv

/-- The child stream is produced by the first item, not the outer stream's later failure.
Witness: its exact generated location and producer projection.
-/
private theorem child_located
    : Located work [0, 0, 1, 0, 0, 0, 1] (.stream child childEntries) (some parent)
        [] := by cbv

/-- The child descriptor retains that published item as its structural producer. -/
private theorem child_known : NodeAt work child .stream [] (some parent) :=
  NodeAt.stream child_located

/-- The successful item and subsequent stream failure obey the existing source contract.
Witness: exact item payload/lowering, root readiness, and failure at the next ordinal.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have itemMatches : first.MatchesWork work := by
    intro item member
    have same := List.mem_singleton.mp member
    subst item
    exact ⟨[outer.key], none, TaskAt.item outer_located rfl, by cbv⟩
  have initial : ValidGraphEvents work [first] :=
    .append .nil itemMatches (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, outer_located, by simp, by simp,
        (by intro source impossible; cases impossible), rfl⟩
  refine ⟨.append initial ?_ ?_ ?_, by cbv⟩
  · exact ⟨_, _, _, _, outer_located, .empty, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · simp [first, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, outer_located,
      (by intro source impossible; cases impossible), .empty, rfl⟩

/-- Actual output announces the child with its producer, then closes only the outer stream.
Witness: execute the normalized runner; the still-active child prevents termination.
-/
theorem output
    : atoms = [.streamValues outer [⟨value, 0⟩] [] [child], .streamFailure outer 1] := by
  cbv

/-- The retained cut names an actual fixed failed item, not a hypothetical cancellation.
Witness: its located error payload in the generated outer stream.
-/
private theorem failed_payloads (cut occurrence) (member : (cut, occurrence) ∈ cuts)
    : ∃ owners producer payload,
        TaskAt work occurrence owners producer payload
        ∧ payload.failure.isSome = true := by
  have same : cut = 1 ∧ occurrence = failedItem := by
    simpa only [cuts, List.mem_singleton, Prod.mk.injEq] using member
  rcases same with ⟨rfl, rfl⟩
  exact ⟨[outer.key], none, _, TaskAt.item outer_located rfl, rfl⟩

/-- The actual history has supported publication without using any event-admission premise.
Witness: its only value is the producer-free first item, emitted before the failure cut.
-/
private theorem supported : PublicationSupport work matching atoms cuts := by
  intro index event selected isValue
  cases index with
  | zero =>
      have same : event = .streamValues outer [⟨value, 0⟩] [] [child] := by
        simpa [output] using selected.symm
      subst event
      refine ⟨[outer.key], none, _, outer.key, TaskAt.item outer_located rfl,
        rfl, List.mem_cons_self, ?_, ?_⟩
      · rintro ⟨cut, member, reached, _⟩
        have same : cut = 1 := by simpa [cuts] using member
        simp [same] at reached
      · intro source impossible; cases impossible
  | succ index =>
      cases index with
      | zero =>
          have same : event = .streamFailure outer 1 := by
            simpa [output] using selected.symm
          subst event
          cases isValue
      | succ index => simp [output] at selected

/-- The actual producer publication is retained by the common matching.
Witness: the first value atom has the source item's exact occurrence label.
-/
private theorem parent_published : Published matching atoms parent :=
  ⟨0, .streamValues outer [⟨value, 0⟩] [] [child], by rw [output]; rfl, trivial, rfl⟩

/-- The outer stream's later failure does not cancel its already-published producing item.
Witness: exact failure causality and the derived no-revival theorem on actual support.
-/
theorem parent_survives
    : NodeFailed work matching atoms cuts outer.key
      ∧ ¬TaskCancelled work matching atoms cuts parent := by
  refine ⟨
    NodeFailed.task (TaskAt.item outer_located (index := 1) rfl)
      List.mem_cons_self (by simp [failedBefore, cuts, failedItem, output]),
    ?_
  ⟩
  intro cancelled
  exact supported.cancelled_unpublished failed_payloads cancelled parent_published

/-- The produced child stays healthy despite its enclosing stream's historical failure.
Witness: support-based stream decomposition excludes producer cancellation using the
earlier publication, excludes direct failure by task uniqueness, and uses empty defer
dependencies. This applies the general bridge without Explains or FailureWitness.
-/
theorem child_survives : ¬NodeFailed work matching atoms cuts child.key := by
  apply supported.streamHealthy generated failed_payloads child_known
    (by intro source same; cases same; exact parent_published) ?_ (.inl rfl)
  intro occurrence owners ⟨producer, payload, known⟩ owner failed
  have same : occurrence = failedItem := by
    simpa [failedBefore, cuts, output] using failed
  subst occurrence
  have exactTask : TaskAt work failedItem [outer.key] none (.item outer (.error 1)) :=
    TaskAt.item outer_located rfl
  rw [(known.unique exactTask).1] at owner
  simp [outer, child] at owner

/-- Historical and snapshot failure/cancellation agree for this unassumed actual history.
Witness: apply both general transports, retaining the nonempty cut and published parent.
-/
theorem snapshot_agreement
    : (∀ key,
        NodeFailed work matching atoms cuts key
        ↔ Causality.NodeFailed work (failedBefore cuts atoms.length)
            (Published matching atoms) key)
      ∧ (∀ occurrence,
          TaskCancelled work matching atoms cuts occurrence
          ↔ Causality.TaskCancelled work (failedBefore cuts atoms.length)
              (Published matching atoms) occurrence) :=
  ⟨
    fun _ => supported.nodeFailed_iff_snapshot failed_payloads,
    fun _ => supported.taskCancelled_iff_snapshot failed_payloads
  ⟩

-----------------------------------------------------------------------------------------
-- The healthy produced stream can actually publish next without a cancellation premise
-----------------------------------------------------------------------------------------

private def nextItem : GraphEvent :=
  .streamItems child [⟨childItem, ⟨.scalar "x", 0⟩, {}⟩]

private def nextEvent : WorkQueueEvent := .streamValues child [⟨.scalar "x", 0⟩] [] []

/-- The child's next arrival is valid even after the outer stream has failed.
Witness: its own stream remains started, its producer is the earlier successful item,
and its first ordinal has not been received or closed. No admission premise is used.
-/
theorem next_source_valid
    : ValidGraphEvents work (inputs ++ [[nextItem]]).flatten
      ∧ inputsStarted work (inputs ++ [[nextItem]]) = true := by
  refine ⟨?_, by cbv⟩
  change ValidGraphEvents work (inputs.flatten ++ [nextItem])
  apply ValidGraphEvents.append source_valid.1
  · intro item member
    have same := List.mem_singleton.mp member
    subst item
    exact ⟨[child.key], some parent, TaskAt.item child_located rfl, by cbv⟩
  · simp [nextItem, inputs, first, GraphEvent.Fresh, GraphEvent.identities,
      childItem, parent, outer, child]
  · exact ⟨_, _, _, _, child_located, by simp,
      (by simp [inputs, first, GraphEvent.identities, outer, child]),
      (by intro source equal; cases equal; exact List.mem_cons_self), by cbv⟩

/-- The produced stream's next output really follows the outer-stream failure.
Witness: evaluation of the same runner extended with the child item settlement.
-/
theorem next_output
    : ((State.initialize (Work.fromExecution work)).runNormalized
        (inputs ++ [[nextItem]])).2.flatten.flatMap
        publicationAtoms
      = atoms ++ [nextEvent] := by
  cbv

/-- The next child's full readiness follows from support of only the earlier prefix.
Witness: actual child health and earlier producer publication extend the certificate;
freshness and ordinal zero then derive CanPublish without assuming noncancellation.
-/
theorem next_ready : CanPublish work matching atoms cuts childItem (some parent) := by
  have source : TaskAt work (matching atoms.length) [child.key] (some parent)
      (.item child (.ok (.scalar "x", 0))) := by
    simpa only [output, List.length_cons, List.length_nil, matching, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, childItem]
      using (TaskAt.item child_located (index := 0) rfl)
  have same : matching atoms.length = childItem := by rw [output]; rfl
  rw [← same]
  apply supported.canPublish_next (event := nextEvent) failed_payloads trivial source rfl
    List.mem_cons_self child_survives
    (by intro producer equal; cases equal; exact parent_published)
  · rintro ⟨index, event, selected, value, matched⟩
    cases index with
    | zero =>
        rw [same] at matched
        simp [matching, parent, childItem] at matched
    | succ index =>
        cases index with
        | zero =>
            have equal : event = .streamFailure outer 1 := by
              simpa [output] using selected.symm
            subst event
            cases value
        | succ index => simp [output] at selected
  · intro address first second equal smaller
    rw [same] at equal
    have ordinal : second = 0 := (Occurrence.item.inj equal).2.symm
    omega

-----------------------------------------------------------------------------------------
-- General nested-item safety now derives the certificate instead of assuming support
-----------------------------------------------------------------------------------------

/-- The child item has an item-only lineage of depth two in the generated work.
Witness: its producer is the first outer item; both stream descriptors have empty defer
dependencies. This is structural metadata, not a cancellation or output-admission premise.
-/
theorem child_lineage : ItemLineage work childItem := by
  apply ItemLineage.step (TaskAt.item child_located rfl) child_known
  intro source same
  cases same
  exact .step (TaskAt.item outer_located rfl) (.stream outer_located)
    (by intro parent impossible; cases impossible)

/-- The child survives an actual earlier outer-stream failure under the canonical witness.
Witness: general successful-item certificates, without a lineage or publication-support
premise. Batching, announcements, and the nonempty failure inventory share one matching.
-/
theorem nested_item_certificates
    : ∃ w : ConformancePlan.Witness,
        w.events = atoms ++ [nextEvent]
        ∧ ConformancePlan.BatchShape work (inputs ++ [[nextItem]]) w
        ∧ ConformancePlan.AnnouncedFailures work w
        ∧ w.failures ≠ []
        ∧ ¬TaskCancelled work w.matching w.events w.failures childItem := by
  obtain ⟨w, history, batching, announced, safe⟩ :=
    ConformancePlan.successfulItemCertificates generated next_source_valid.1 next_source_valid.2
  have sameHistory : w.events = atoms ++ [nextEvent] := by
    rw [history]
    cbv
  refine ⟨w, sameHistory, batching, announced, ?_, ?_⟩
  · intro empty
    have atFailure : w.events[1]? = some (.streamFailure outer 1) := by
      rw [sameHistory, output]
      rfl
    have count := announced.1.2.2.2.2 1 outer 1 atFailure
    simp [empty, failedBefore, NodeErrors] at count
  · apply safe _ _
    simp [inputs, nextItem, first, childItem, GraphEvent.successes]

-----------------------------------------------------------------------------------------
-- Successful nested completion remains admitted after the outer stream fails
-----------------------------------------------------------------------------------------

private def completedInputs : List (List GraphEvent) :=
  inputs ++ [[nextItem], [.streamSuccess child]]

/-- The child can complete successfully after its only item, despite the outer failure.
Witness: exact exhausted cursor, fresh child closure, prior producer success, and actual
queue starts; no health or output-admission property is assumed in source validity.
-/
theorem completion_source_valid
    : ValidGraphEvents work completedInputs.flatten
      ∧ inputsStarted work completedInputs = true := by
  refine ⟨?_, by cbv⟩
  change ValidGraphEvents work ((inputs ++ [[nextItem]]).flatten ++ [.streamSuccess child])
  apply ValidGraphEvents.append next_source_valid.1
  · exact ⟨[], some parent, ⟨_, _, child_located⟩⟩
  · simp [inputs, first, nextItem, GraphEvent.Fresh, GraphEvent.identities, outer, child]
  · exact ⟨_, _, _, _, child_located,
      (by intro source same; cases same; exact List.mem_cons_self), by cbv⟩

/-- The failed outer closure and successful child closure share full local admission.
Witness: the general mixed construction retains the actual nested publication history,
then derives both closure rules on one matching and failure inventory. This does not
assert admission of the notice-carrying value events themselves.
-/
theorem completion_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events = atoms ++ [nextEvent, .streamSuccess child]
        ∧ ConformancePlan.BatchShape work completedInputs w
        ∧ FailureWitness work (ConformancePlan.initialKeys work)
            w.matching w.events w.failures
        ∧ ConformancePlan.FailureAdmission work w
        ∧ ConformancePlan.StreamSuccessAdmission work w := by
  obtain ⟨w, history, shape, announced, uncancelled, failed, successful⟩ :=
    ConformancePlan.streamAndFailureAdmission_certificates generated completion_source_valid.1
      completion_source_valid.2
  refine ⟨w, ?_, shape, ConformancePlan.failureWitness announced uncancelled,
    failed, successful⟩
  rw [history]
  cbv

/-- The child's notice-free item satisfies full admission after its outer stream fails.
Witness: the general joint construction supplies provenance, causal readiness, and owner
selection on the same licensed mixed history; empty child notices finish the exact rule.
-/
theorem child_publication_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events = atoms ++ [nextEvent]
        ∧ ConformancePlan.BatchShape work (inputs ++ [[nextItem]]) w
        ∧ FailureWitness work (ConformancePlan.initialKeys work)
            w.matching w.events w.failures
        ∧ EventAllowed work (ConformancePlan.initialKeys work) w.matching
            (w.events.take 2) w.failures nextEvent := by
  obtain ⟨w, history, shape, announced, uncancelled, _, _, ready⟩ :=
    ConformancePlan.mixed_eventCertificates generated next_source_valid.1 next_source_valid.2
  have exactHistory : w.events = atoms ++ [nextEvent] := by rw [history]; cbv
  refine ⟨
    w,
    exactHistory,
    shape,
    ConformancePlan.failureWitness announced uncancelled,
    ?_
  ⟩
  apply ConformancePlan.streamValueAllowed_without_notices ready
  rw [exactHistory, output]
  rfl

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerSupportedCausality
