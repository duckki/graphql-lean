import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.PublicationOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureExtension

/-! Structural producer and stream-order dependencies cannot themselves strand work.
Notice eligibility and owner availability are separate from the readiness proved here.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- A well-founded measure of structural dependencies
-----------------------------------------------------------------------------------------

/-- Weight an absolute work address by positive edge indices. Stream-item edges retain
enough weight to place a producer before any task inside that item's child work.
-/
def addressRank (address : Address) : Nat := (address.map (· + 1)).sum

/-- A proof-only rank: producers and preceding stream items have smaller ranks.
Unrelated tasks may have equal ranks; this imposes no scheduler ordering on them.
-/
def Occurrence.dependencyRank : Occurrence → Nat
  | .executionGroup address => addressRank address
  | .item address index => addressRank address + index

/-- Descending one edge strictly increases the base address rank. Witness: the positive
last summand, including the selected item ordinal on stream-child edges.
-/
theorem addressRank_snoc (address : Address) (index : Nat)
    : addressRank (address ++ [index]) = addressRank address + index + 1 := by
  simp [addressRank, List.sum_append, Nat.add_assoc]

/-- Every located producer precedes the entire located subtree in dependency rank.
Witness: structural navigation; task-generating edges strictly increase address weight.
-/
theorem Located.producer_rank {work address current producer owners}
    (located : Located work address current producer owners)
    {producerOccurrence} (generated : producer = some producerOccurrence)
    : producerOccurrence.dependencyRank < addressRank address := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => contradiction
  | left _ ih | right _ ih =>
      have earlier := ih generated
      rw [addressRank_snoc]
      omega
  | executionGroup =>
      cases generated
      simp [Occurrence.dependencyRank, addressRank_snoc]
  | item =>
      cases generated
      simp [Occurrence.dependencyRank, addressRank_snoc]

/-- A located producer is an actual task, not merely an address annotation. Witness:
the generating deferred/item edge, preserved through subsequent combine navigation.
-/
theorem Located.producer_known {work address current producer owners}
    (located : Located work address current producer owners)
    {producerOccurrence} (generated : producer = some producerOccurrence)
    : ∃ producerOwners ancestor payload,
        TaskAt work producerOccurrence producerOwners ancestor payload := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => contradiction
  | left _ ih | right _ ih => exact ih generated
  | executionGroup located =>
      cases generated
      exact ⟨_, _, _, .executionGroup located.toCurrent⟩
  | item located selected =>
      cases generated
      exact ⟨_, _, _, .item located.toCurrent selected⟩

/-- A task's producer exists and has strictly smaller dependency rank. Witness:
the producer facts for the task's unique located work boundary.
-/
theorem TaskAt.producer_dependency {work occurrence owners producerOccurrence payload}
    (known : TaskAt work occurrence owners (some producerOccurrence) payload)
    : producerOccurrence.dependencyRank < occurrence.dependencyRank
      ∧ ∃ producerOwners ancestor result,
          TaskAt work producerOccurrence producerOwners ancestor result := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located => exact ⟨located.toCurrent.producer_rank rfl,
      located.toCurrent.producer_known rfl⟩
  | item located selected =>
      have lower := located.toCurrent.producer_rank rfl
      exact ⟨
        by simp only [Occurrence.dependencyRank] at lower ⊢; omega,
        located.toCurrent.producer_known rfl
      ⟩

-----------------------------------------------------------------------------------------
-- Cancellation respects shared structural prerequisites
-----------------------------------------------------------------------------------------

/-- Unpublished tasks with identical owners and producer share cancellation causes.
Witness: retain the original cut and rebuild its causal rule for the second task.
-/
theorem TaskCancelled.same_prerequisites
    {work matching events failures occurrence other owners producer payload result}
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence owners producer payload)
    (next : TaskAt work other owners producer result)
    (unpublished : ¬Published matching events other)
    : TaskCancelled work matching events failures other := by
  obtain ⟨cut, member, reached, cause⟩ := cancelled
  have absent : ¬Published matching (events.take cut) other := by
    intro published
    apply unpublished
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  refine ⟨cut, member, reached, ?_⟩
  cases cause with
  | owners projected _ nonempty failures =>
      obtain ⟨ancestor, value, descriptor⟩ := projected
      have equal := (TaskAt.unique descriptor known).1
      exact Causality.TaskCancelled.owners ⟨_, _, next⟩ absent
        (equal ▸ nonempty) (equal ▸ failures)
  | producerFailed projected _ failure =>
      obtain ⟨producerOwners, value, descriptor⟩ := projected
      have equal := (TaskAt.unique descriptor known).2.1
      exact Causality.TaskCancelled.producerFailed ⟨_, _, equal ▸ next⟩ absent failure
  | producerCancelled projected _ failure =>
      obtain ⟨producerOwners, value, descriptor⟩ := projected
      have equal := (TaskAt.unique descriptor known).2.1
      exact Causality.TaskCancelled.producerCancelled ⟨_, _, equal ▸ next⟩ absent failure

/-- A noninitial stream task has a predecessor with the same owners and producer.
Witness: the preceding valid index in the exact same stream item list.
-/
theorem TaskAt.predecessor {work address index owners producer payload}
    (known : TaskAt work (.item address (index + 1)) owners producer payload)
    : ∃ previous, TaskAt work (.item address index) owners producer previous := by
  obtain ⟨node, items, enclosing, result, children, located, selected, rfl, rfl⟩ := known
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have prior : index < items.length := by omega
  obtain ⟨value, work⟩ := items[index]
  exact ⟨_, .item located (List.getElem?_eq_getElem prior)⟩

-----------------------------------------------------------------------------------------
-- Some outstanding task has satisfied structural dependencies
-----------------------------------------------------------------------------------------

/-- If any task is not accounted for, some task is ready with respect to producers and
stream order. Witness: descend to an unaccounted producer or preceding item; dependency
rank strictly decreases. Owner/notice availability is deliberately not asserted here.
-/
theorem readyTask_exists {work matching events failed occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (outstanding : ¬TaskAccounted work matching events failed occurrence)
    : ∃ next nextOwners nextProducer result,
        TaskAt work next nextOwners nextProducer result
        ∧ CanPublish work matching events failed next nextProducer := by
  classical
  induction rank : occurrence.dependencyRank
    using Nat.strongRecOn generalizing occurrence owners producer payload with
  | ind rank ih =>
      have active : ¬TaskCancelled work matching events failed occurrence := fun cancelled =>
        outstanding (Or.inl cancelled)
      have fresh : ¬Published matching events occurrence := fun published =>
        outstanding (Or.inr published)
      by_cases generated : ∀ producerOccurrence,
          producer = some producerOccurrence
          → Published matching events producerOccurrence
      · have readyExceptItems := And.intro fresh (And.intro active generated)
        cases occurrence with
        | executionGroup address => exact ⟨_, _, _, _, known,
            ⟨readyExceptItems.1, readyExceptItems.2.1, readyExceptItems.2.2, trivial⟩⟩
        | item address index =>
            cases index with
            | zero => exact ⟨_, _, _, _, known,
                ⟨readyExceptItems.1, readyExceptItems.2.1, readyExceptItems.2.2, trivial⟩⟩
            | succ index =>
                obtain ⟨previous, prior⟩ := known.predecessor
                by_cases accounted :
                  TaskAccounted work matching events failed (.item address index)
                · rcases accounted with cancelled | published
                  · exact False.elim (active (cancelled.same_prerequisites prior known fresh))
                  · exact ⟨_, _, _, _, known, ⟨fresh, active, generated, published⟩⟩
                · apply ih (Occurrence.item address index).dependencyRank
                    (by simp only [Occurrence.dependencyRank] at rank ⊢; omega)
                    prior accounted rfl
      · obtain ⟨producerOccurrence, produces, unpublished⟩ :=
          Classical.not_forall.mp generated
          |>.imp fun _ h => not_imp.mp h
        subst producer
        obtain ⟨lower, producerOwners, ancestor, result, producerKnown⟩ :=
          known.producer_dependency
        have unaccounted
            : ¬TaskAccounted work matching events failed producerOccurrence := by
          rintro (cancelled | published)
          · exact active (.producerCancelled known fresh cancelled)
          · exact unpublished published
        exact ih producerOccurrence.dependencyRank (by omega) producerKnown unaccounted rfl

/-- Every published task has a successful structural producer chain. Witness: recurse
through the strictly earlier producer publication supplied by the event admission rule.
-/
theorem Explains.publication_reachable {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {index event} (selected : events[index]? = some event) (value : IsValue event)
    : Reachable work (matching index) := by
  induction index using Nat.strongRecOn generalizing event with
  | ind index ih =>
      obtain ⟨owners, producer, payload, known, _⟩ :=
        explained.published_task ⟨index, event, selected, value, rfl⟩
      cases producer with
      | none => exact .root ⟨owners, payload, known⟩
      | some producerOccurrence =>
          obtain ⟨earlier, previous, less, prior, publishes, same⟩ :=
            explained.producer_before selected value known
          obtain ⟨producerOwners, ancestor, result, producerKnown, success⟩ :=
            explained.published_task ⟨earlier, previous, prior, publishes, same⟩
          exact .child ⟨owners, payload, known⟩
            ⟨producerOwners, ancestor, result, producerKnown, success⟩
            (same ▸ ih earlier less prior publishes)

/-- A structurally ready task after an explained history is reachable even if its own
outcome fails. Witness: its root status or its already-published successful producer.
-/
theorem CanPublish.reachable
    {work groups streams events matching failures occurrence owners producer payload}
    (ready : CanPublish work matching events failures occurrence producer)
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload)
    : Reachable work occurrence := by
  cases producer with
  | none => exact .root ⟨owners, payload, known⟩
  | some producerOccurrence =>
      have published := ready.2.2.1 producerOccurrence rfl
      obtain ⟨producerOwners, ancestor, result, producerKnown, success⟩ :=
        explained.published_task published
      obtain ⟨index, event, selected, value, same⟩ := published
      exact .child ⟨owners, payload, known⟩
        ⟨producerOwners, ancestor, result, producerKnown, success⟩
        (same ▸ explained.publication_reachable selected value)

/-- Cancelling every producer-free task cancels every task in finite raw work.
Witness: strong induction on dependency rank, transporting a smaller producer's
cancellation to each child. No publication order or source implementation is chosen.
-/
theorem all_tasks_cancelled_of_roots {work matching events failures}
    (unpublished : ∀ occurrence, ¬Published matching events occurrence)
    (roots
      : ∀ occurrence owners payload,
          TaskAt work occurrence owners none payload
          → TaskCancelled work matching events failures occurrence)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : TaskCancelled work matching events failures occurrence := by
  generalize rankEq : occurrence.dependencyRank = rank
  induction rank
    using Nat.strongRecOn generalizing occurrence owners producer payload with
  | ind rank ih =>
      cases producer with
      | none => exact roots occurrence owners payload known
      | some producerOccurrence =>
          obtain ⟨smaller, producerOwners, ancestor, result, producerKnown⟩ :=
            known.producer_dependency
          apply TaskCancelled.producerCancelled known (unpublished _)
          exact ih producerOccurrence.dependencyRank (by omega) producerKnown rfl

-----------------------------------------------------------------------------------------
-- An outstanding task has a healthy, uncompleted owner
-----------------------------------------------------------------------------------------

/-- Every contributing owner is a real delivery node. Witness: its deferred fragment or
the stream item's exact stream descriptor, not an ancestor placeholder.
-/
theorem TaskAt.owner_at_producer {work occurrence owners producer payload key}
    (known : TaskAt work occurrence owners producer payload) (member : key ∈ owners)
    : ∃ node kind dependencies,
        NodeAt work node kind dependencies producer ∧ node.key = key := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨group, inGroups, equal⟩ := List.mem_map.mp member
      exact ⟨group.node, .group, _, .group located.toCurrent inGroups, equal⟩
  | item located selected =>
      exact ⟨_, .stream, _, .stream located.toCurrent,
        (List.mem_singleton.mp member).symm⟩

/-- Forgetting the exact producer retains structural support for every task owner.
Witness: the owner descriptor at the task's own producer boundary.
-/
theorem TaskAt.owner_known {work occurrence owners producer payload key}
    (known : TaskAt work occurrence owners producer payload) (member : key ∈ owners)
    : ∃ node kind dependencies birth,
        NodeAt work node kind dependencies birth ∧ node.key = key := by
  obtain ⟨node, kind, dependencies, descriptor, same⟩ := known.owner_at_producer member
  exact ⟨node, kind, dependencies, producer, descriptor, same⟩

/-- Failure evidence at an earlier boundary is included at every later boundary.
Witness: the same recorded cut still satisfies the larger prefix-length bound.
-/
theorem failedBefore_subset (failures : FailureCuts) {earlier later : Nat}
    (before : earlier ≤ later)
    : (failedBefore failures earlier).Subset (failedBefore failures later) := by
  intro occurrence member
  obtain ⟨entry, inFilter, rfl⟩ := List.mem_map.mp member
  obtain ⟨inCuts, bounded⟩ := List.mem_filter.mp inFilter
  exact List.mem_map.mpr
    ⟨
      entry,
      List.mem_filter.mpr ⟨inCuts, by simp only [decide_eq_true_eq] at bounded ⊢; omega⟩,
      rfl
    ⟩

/-- Task accounting at an earlier event prefix remains valid at the current boundary.
Witness: causal failure monotonicity or the unchanged earlier publication index.
-/
theorem TaskAccounted.take_prefix {work matching events failures index occurrence}
    (accounted : TaskAccounted work matching (events.take index) failures occurrence)
    (_bounded : index ≤ events.length)
    : TaskAccounted work matching events failures occurrence := by
  rcases accounted with cancelled | published
  · exact Or.inl (by
      simpa only [List.take_append_drop] using cancelled.append (events.drop index))
  · obtain ⟨position, event, _, selected, value, same⟩ := published.before
    exact Or.inr ⟨position, event, selected, value, same⟩

/-- A completed key is either failed or has all contributing tasks accounted for at the
current boundary. Witness: its actual success/failure event, transported along the prefix.
-/
theorem Explains.completed_accounted {work groups streams events matching failures key}
    (explained : Explains work groups streams events matching failures)
    (closed : key ∈ completedKeys events)
    : NodeFailed work matching events failures key
      ∨ NodeAccounted work matching events failures key := by
  obtain ⟨event, member, completes⟩ := List.mem_flatMap.mp closed
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have bound := Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1
  have allowed := explained.2.2 index event selected
  cases event <;> simp only [eventCompleted, List.mem_singleton, List.not_mem_nil] at completes
  all_goals try contradiction
  all_goals subst key
  all_goals simp only [EventAllowed, NodeAccounted, TaskAccounted,
    nodeFailed_filter (Nat.le_refl _), taskCancelled_filter (Nat.le_refl _)] at allowed
  case groupSuccess node newGroups newStreams =>
    exact Or.inr (fun occurrence owners known contributes =>
      TaskAccounted.take_prefix (allowed.2.2.2.1 occurrence owners known contributes) bound)
  case streamSuccess node =>
    exact Or.inr (fun occurrence owners known contributes =>
      TaskAccounted.take_prefix (allowed.2.2.2 occurrence owners known contributes) bound)
  case groupFailure node errors =>
    exact Or.inl
      (by
        simpa only [List.take_append_drop] using allowed.2.2.1.append (events.drop index))
  case streamFailure node errors =>
    exact Or.inl
      (by
        simpa only [List.take_append_drop] using allowed.2.2.1.append (events.drop index))

/-- Any unaccounted task with nonempty owners has a healthy owner which has not closed.
Witness: otherwise all owners cancel the task, or a healthy completion already accounts
for it. The owner may still be unannounced; readiness alone does not guarantee a notice.
-/
theorem Explains.outstanding_owner
    {work groups streams events matching failures occurrence owners producer payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload) (nonempty : owners ≠ [])
    (outstanding : ¬TaskAccounted work matching events failures occurrence)
    : ∃ key ∈ owners,
        ¬NodeFailed work matching events failures key ∧ key ∉ completedKeys events := by
  classical
  have healthy : ∃ key ∈ owners, ¬NodeFailed work matching events failures key := by
    apply Classical.byContradiction
    intro absent
    apply outstanding
    apply Or.inl
    apply explained.snapshot_taskCancelled
    refine Causality.TaskCancelled.owners ⟨_, _, known⟩
      (fun published => outstanding (Or.inr published)) nonempty ?_
    intro key member
    apply explained.nodeFailed_snapshot
    apply Classical.byContradiction
    intro healthy
    exact absent ⟨key, member, healthy⟩
  obtain ⟨key, member, healthy⟩ := healthy
  refine ⟨key, member, healthy, ?_⟩
  intro closed
  rcases explained.completed_accounted closed with failed | accounted
  · exact healthy failed
  · exact outstanding (accounted occurrence owners ⟨producer, payload, known⟩ member)

end GraphQL.IncrementalDelivery.WorkQueueSemantics
