import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.TaskReadiness
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.PublicationExtension
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.CompletionExistence

/-! Generated path coherence turns an announced healthy owner into a permitted task step.
Notice availability is an explicit local hypothesis here, not a scheduler invariant.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Longest-path ownership does not prevent an available task from publishing
-----------------------------------------------------------------------------------------

/-- An available contributing owner has a longest-path representative for coherent work.
Witness: all owner paths are prefixes of the fixed payload path, so eligible lengths
form a nonempty bounded finite set. Equal-length choices remain nondeterministic.
-/
theorem owner_exists_of_available
    {paths bound work occurrence owners producer payload initial events failed}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (known : TaskAt work occurrence owners producer payload)
    (available : ∃ node, AvailableOwner work initial events failed owners node)
    : ∃ node, Owner work initial events failed owners node := by
  classical
  let eligible (length : Nat) := ∃ node,
    AvailableOwner work initial events failed owners node ∧ node.path.length = length
  let lengths := (List.range ((payloadPath payload).length + 1)).filter
    (fun length => decide (eligible length))
  have bounded {node} (active : AvailableOwner work initial events failed owners node)
      : node.path.length ≤ (payloadPath payload).length := by
    obtain ⟨kind, dependencies, producerOccurrence, located⟩ := active.1
    obtain ⟨suffix, equal⟩ := workAt_owner_prefix coherent known located active.2.1
    change payloadPath payload = node.path ++ suffix at equal
    simp only [equal, List.length_append]
    omega
  have member {node} (active : AvailableOwner work initial events failed owners node)
      : node.path.length ∈ lengths := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by have := bounded active; omega),
      by simpa only [decide_eq_true_eq] using (show eligible node.path.length from
        ⟨node, active, rfl⟩)⟩
  obtain ⟨candidate, active⟩ := available
  obtain ⟨length, maximum⟩ := Option.isSome_iff_exists.mp
    (List.isSome_max?_of_mem (member active))
  have greatest := List.max?_eq_some_iff.mp maximum
  have eligibleLength : eligible length := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp greatest.1).2
  obtain ⟨node, active, equal⟩ := eligibleLength
  exact ⟨node, active, fun other present => equal ▸ greatest.2 _ (member present)⟩

/-- A stream item's own node is a permitted owner whenever its key is open and healthy.
Witness: its sole owner key and coherent paths make every alternative descriptor's path
the same length, rather than requiring descriptor uniqueness.
-/
theorem stream_owner_of_open
    {paths bound work occurrence owners producer node result initial events failed}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (known : TaskAt work occurrence owners producer (.item node result))
    (opened : Open initial events node.key) (healthy : ¬NodeFailed work failed node.key)
    : Owner work initial events failed owners node := by
  cases StructuralEquivalence.taskAt_of_current known with
  | item located selected =>
      have streamKnown := NodeAt.stream located.toCurrent
      refine ⟨⟨⟨.stream, _, _, streamKnown⟩, by simp, opened, healthy⟩, ?_⟩
      intro other available
      obtain ⟨kind, dependencies, producerOccurrence, otherKnown⟩ := available.1
      have equal := workAt_same_path coherent otherKnown streamKnown
        (List.mem_singleton.mp available.2.1)
      simp only [equal, Nat.le_refl]

/-- A ready task's owner cannot yet satisfy a dependency.
Witness: it is represented work; completion or silent accounting would account for the
still-unpublished, uncancelled task. This fact permits arbitrary shared owner lists.
-/
theorem ready_owner_dependency_unsatisfied
    {work groups streams events matching failures occurrence owners producer payload key}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload) (member : key ∈ owners)
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    : ¬DependencySatisfied work ((groups ++ streams).map DeliveryNode.key) matching events
        (failedBefore failures events.length) key := by
  rintro ⟨healthy, absent | completed | ⟨_, accounted⟩⟩
  · obtain ⟨node, kind, dependencies, descriptor, same⟩ :=
      known.owner_at_producer member
    exact absent ⟨producer, node, kind, dependencies, descriptor, same⟩
  · rcases explained.completed_accounted completed with failed | accounted
    · exact healthy failed
    · rcases accounted occurrence owners ⟨producer, payload, known⟩ member
        with cancelled | published
      · exact ready.2.1 cancelled
      · exact ready.1 published
  · rcases accounted occurrence owners ⟨producer, payload, known⟩ member
      with cancelled | published
    · exact ready.2.1 cancelled
    · exact ready.1 published

-----------------------------------------------------------------------------------------
-- Constructing a step from a ready, announced task
-----------------------------------------------------------------------------------------

/-- A ready task with an announced healthy owner can extend the actual explained history.
Witness: longest-path object ownership or exact stream ownership for successful outcomes;
reachable failing outcomes instead append a justified cut and counted failure completion.
No success or error-positivity premise is required.
-/
theorem extend_ready_announced
    {paths bound work groups streams events matching failures
      occurrence owners producer payload}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload)
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    (announced
      : ∃ key ∈ owners,
          key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events
          ∧ ¬NodeFailed work (failedBefore failures events.length) key)
    : ∃ event next cuts, Explains work groups streams (events ++ [event]) next cuts := by
  obtain ⟨key, member, notified, healthy⟩ := announced
  have outstanding : ¬Accounted work matching events
      (failedBefore failures events.length) occurrence := by
    rintro (cancelled | published)
    · exact ready.2.1 cancelled
    · exact ready.1 published
  have opened : Open ((groups ++ streams).map DeliveryNode.key) events key := by
    refine ⟨notified, ?_⟩
    intro closed
    rcases explained.completed_accounted closed with failure | accounted
    · exact healthy failure
    · exact outstanding (accounted occurrence owners ⟨producer, payload, known⟩ member)
  have failing (fails : payload.failure.isSome = true) :
      ∃ event next cuts, Explains work groups streams (events ++ [event]) next cuts := by
    obtain ⟨node, errors, event, _, _, _, extended⟩ := explained.failure_step known fails
      (ready.reachable explained known) ⟨key, member, opened⟩
      (by simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)] using ready.2.1)
    exact ⟨event, matching, _, extended⟩
  cases payload with
  | object path result =>
      cases result with
      | error errors => exact failing rfl
      | ok value =>
          obtain ⟨data, errors⟩ := value
          obtain ⟨node, kind, dependencies, nodeProducer, nodeKnown, same⟩ :=
            known.owner_known member
          have available : AvailableOwner work ((groups ++ streams).map DeliveryNode.key)
              events (failedBefore failures events.length) owners node :=
            ⟨⟨kind, dependencies, nodeProducer, nodeKnown⟩, same ▸ member,
              same ▸ opened,
              same ▸ healthy⟩
          obtain ⟨owner, selected⟩ := owner_exists_of_available coherent known ⟨node, available⟩
          exact ⟨_, _, _, explained.publish_object known ready selected⟩
  | item node result =>
      cases result with
      | error errors => exact failing rfl
      | ok value =>
          obtain ⟨item, errors⟩ := value
          have ownerKey : key = node.key := by
            cases StructuralEquivalence.taskAt_of_current known with
            | item located selected => exact List.mem_singleton.mp member
          have selected := stream_owner_of_open coherent known (ownerKey ▸ opened)
            (ownerKey ▸ healthy)
          exact ⟨_, _, _, explained.publish_item known ready selected⟩

-----------------------------------------------------------------------------------------
-- What can still block a maximal history?
-----------------------------------------------------------------------------------------

/-- A maximal history with outstanding work has a structurally ready task whose healthy
owners are all unannounced. Witness: well-founded readiness and the preceding extension
theorem; an announced healthy owner would construct a forbidden extra event.
-/
theorem maximal_outstanding_unannounced
    {paths bound work groups streams events matching failures occurrence owners producer
      payload}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (maximal
      : ∀ event next cuts, ¬Explains work groups streams (events ++ [event]) next cuts)
    (known : TaskAt work occurrence owners producer payload)
    (outstanding
      : ¬Accounted work matching events (failedBefore failures events.length) occurrence)
    : ∃ next nextOwners nextProducer result,
        TaskAt work next nextOwners nextProducer result
        ∧ CanPublish work matching events (failedBefore failures events.length) next
            nextProducer
        ∧ ∀ key ∈ nextOwners,
            ¬NodeFailed work (failedBefore failures events.length) key
            → key ∉ announcedKeys ((groups ++ streams).map DeliveryNode.key) events := by
  obtain ⟨next, nextOwners, nextProducer, result, task, ready⟩ :=
    readyTask_exists known outstanding
  refine ⟨next, nextOwners, nextProducer, result, task, ready, ?_⟩
  intro key member healthy notified
  obtain ⟨event, nextMatching, cuts, extended⟩ := extend_ready_announced coherent explained
    task ready ⟨key, member, notified, healthy⟩
  exact maximal event nextMatching cuts extended

-----------------------------------------------------------------------------------------
-- Complete runs when the initial frontier covers all task owners
-----------------------------------------------------------------------------------------

/-- If valid initial notices cover every task owner, a complete finite run exists.
Witness: a maximal finite continuation cannot strand an unaccounted task, because its
healthy owner is already announced; constructive finalization then closes all open IDs.
This covers a useful class of work, not general nested fresh-notice execution.
-/
theorem completeRun_exists_of_initial_owner_coverage
    {paths bound work groups streams}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (initialized : Initializes work groups streams)
    (covered
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → owners ≠ [] ∧ ∀ key ∈ owners, key ∈ (groups ++ streams).map DeliveryNode.key)
    : ∃ history, AdmissibleRun work history := by
  classical
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  obtain ⟨events, matching, failures, explained, maximal⟩ := initial.maximal_extension
  simp only [List.nil_append] at explained maximal
  apply (admissibleRun_exists_iff_accounted_history work).mpr
  refine ⟨groups, streams, events, matching, failures, explained, ?_⟩
  intro occurrence owners producer payload known
  apply Classical.byContradiction
  intro outstanding
  obtain ⟨next, nextOwners, nextProducer, result, task, ready, unannounced⟩ :=
    maximal_outstanding_unannounced coherent explained
      (fun event next cuts extended => by
        have impossible := maximal [event] next cuts extended
        cases impossible) known outstanding
  have unaccounted : ¬Accounted work matching events
      (failedBefore failures events.length) next := by
    rintro (cancelled | published)
    · exact ready.2.1 cancelled
    · exact ready.1 published
  obtain ⟨nonempty, announced⟩ := covered next nextOwners nextProducer result task
  obtain ⟨key, member, healthy, _⟩ := explained.outstanding_owner task nonempty unaccounted
  exact unannounced key member healthy (List.mem_append_left _ (announced key member))

end GraphQL.IncrementalDelivery.Correctness
