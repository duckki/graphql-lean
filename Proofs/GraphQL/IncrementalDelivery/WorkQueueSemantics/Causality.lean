import GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Causal evidence at recorded failure cuts and its preservation under observation. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- A reached failure remains in the failures visible at that boundary.
Witness: membership in the filtered list of cuts.
-/
theorem mem_failedBefore {failures cut occurrence index}
    (member : (cut, occurrence) ∈ failures) (before : cut ≤ index)
    : occurrence ∈ failedBefore failures index := by
  exact List.mem_map.mpr
    ⟨(cut, occurrence), List.mem_filter.mpr ⟨member, by simpa using before⟩, rfl⟩

/-- A failed contributing task fails its owner at its recorded cut.
Witness: extract the reached cut and apply the kernel's direct-failure constructor.
-/
theorem NodeFailed.task
    {work matching events failures occurrence owners producer payload ref}
    (known : TaskAt work occurrence owners producer payload) (owner : ref ∈ owners)
    (finished : occurrence ∈ failedBefore failures events.length)
    : NodeFailed work matching events failures ref := by
  obtain ⟨⟨cut, task⟩, member, same⟩ := List.mem_map.mp finished
  obtain ⟨member, bounded⟩ := List.mem_filter.mp member
  dsimp only at same
  subst task
  refine ⟨
    cut,
    List.mem_map.mpr ⟨(cut, occurrence), member, rfl⟩,
    by simpa using bounded,
    ?_
  ⟩
  exact Causality.NodeFailed.task ⟨producer, payload, known⟩ owner
    (mem_failedBefore member (Nat.le_refl _))

/-- A failed defer dependency fails its group at the same cut.
Witness: preserve the cut and extend the kernel derivation.
-/
theorem NodeFailed.groupDependency
    {work matching events failures node dependencies producer ref}
    (known : NodeAt work node .group dependencies producer)
    (dependency : ref ∈ dependencies)
    (failure : NodeFailed work matching events failures ref)
    : NodeFailed work matching events failures node.ref := by
  obtain ⟨cut, member, bounded, cause⟩ := failure
  exact ⟨cut, member, bounded,
    Causality.NodeFailed.groupDependency ⟨node, producer, known, rfl⟩ dependency cause⟩

/-- Cancellation in a cut snapshot excludes publication in that snapshot.
Witness: every kernel cancellation constructor carries the same exclusion.
-/
theorem Causality.TaskCancelled.unpublished {work failed published occurrence}
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    : ¬published occurrence := by
  cases cancelled with
  | owners _ absent _ _ => exact absent
  | producerFailed _ absent _ => exact absent
  | producerCancelled _ absent _ => exact absent

/-- A failure cut retains its publication snapshot after outputs are appended.
Witness: the cut was already bounded by the original prefix.
-/
theorem NodeFailed.append {work matching events failures ref}
    (failure : NodeFailed work matching events failures ref) (tail : List WorkQueueEvent)
    : NodeFailed work matching (events ++ tail) failures ref := by
  obtain ⟨cut, member, bounded, cause⟩ := failure
  refine ⟨cut, member, by simp only [List.length_append]; omega, ?_⟩
  simpa only [List.take_append_of_le_length bounded] using cause

/-- Cancellation remains attached to its original cut after more outputs arrive.
Witness: retain the bounded cut and its unchanged publication snapshot.
-/
theorem TaskCancelled.append {work matching events failures occurrence}
    (cancelled : TaskCancelled work matching events failures occurrence)
    (tail : List WorkQueueEvent)
    : TaskCancelled work matching (events ++ tail) failures occurrence := by
  obtain ⟨cut, member, bounded, cause⟩ := cancelled
  refine ⟨cut, member, by simp only [List.length_append]; omega, ?_⟩
  simpa only [List.take_append_of_le_length bounded] using cause

/-- Restricting failure cuts to a later boundary preserves earlier failure observations;
witness: filter composition and transitivity of cut bounds.
-/
theorem failedBefore_filter (failures : FailureCuts) {index bound : Nat}
    (within : index ≤ bound)
    : failedBefore (failures.filter (fun entry => entry.1 ≤ bound)) index
      = failedBefore failures index := by
  unfold failedBefore
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro entry _
  rw [← Bool.decide_and]
  have same : (entry.1 ≤ index ∧ entry.1 ≤ bound) ↔ entry.1 ≤ index := by omega
  simp only [same]

/-- Truncating future cuts retains each already reached node failure.
Witness: the same cut, unchanged failed occurrences, and unchanged publications.
-/
theorem nodeFailed_filter {work matching events failures bound}
    (within : events.length ≤ bound)
    : NodeFailed work matching events (failures.filter (fun entry => entry.1 ≤ bound))
      = NodeFailed work matching events failures := by
  funext ref
  apply propext
  constructor
  · rintro ⟨cut, member, reached, cause⟩
    obtain ⟨entry, kept, same⟩ := List.mem_map.mp member
    refine ⟨cut, List.mem_map.mpr ⟨entry, (List.mem_filter.mp kept).1, same⟩,
      reached, ?_⟩
    simpa only [failedBefore_filter failures (Nat.le_trans reached within)] using cause
  · rintro ⟨cut, member, reached, cause⟩
    obtain ⟨entry, member, same⟩ := List.mem_map.mp member
    have kept : decide (entry.1 ≤ bound) = true := by
      simpa only [same, decide_eq_true_eq] using (Nat.le_trans reached within)
    refine ⟨cut, List.mem_map.mpr ⟨entry,
      List.mem_filter.mpr ⟨member, kept⟩, same⟩, reached, ?_⟩
    simpa only [failedBefore_filter failures (Nat.le_trans reached within)] using cause

/-- Truncating future cuts retains each already reached task cancellation.
Witness: the same bounded cut and the same causal snapshot.
-/
theorem taskCancelled_filter {work matching events failures bound}
    (within : events.length ≤ bound)
    : TaskCancelled work matching events (failures.filter (fun entry => entry.1 ≤ bound))
      = TaskCancelled work matching events failures := by
  funext occurrence
  apply propext
  constructor
  · rintro ⟨cut, member, reached, cause⟩
    obtain ⟨entry, kept, same⟩ := List.mem_map.mp member
    refine ⟨cut, List.mem_map.mpr ⟨entry, (List.mem_filter.mp kept).1, same⟩,
      reached, ?_⟩
    simpa only [failedBefore_filter failures (Nat.le_trans reached within)] using cause
  · rintro ⟨cut, member, reached, cause⟩
    obtain ⟨entry, member, same⟩ := List.mem_map.mp member
    have kept : decide (entry.1 ≤ bound) = true := by
      simpa only [same, decide_eq_true_eq] using (Nat.le_trans reached within)
    refine ⟨cut, List.mem_map.mpr ⟨entry,
      List.mem_filter.mpr ⟨member, kept⟩, same⟩, reached, ?_⟩
    simpa only [failedBefore_filter failures (Nat.le_trans reached within)] using cause

/-- Cancelling a producer also cancels an unpublished child at the same cut.
Witness: retain the producer's cut and restrict the child's publication exclusion.
-/
theorem TaskCancelled.producerCancelled
    {work matching events failures occurrence owners producer payload}
    (known : TaskAt work occurrence owners (some producer) payload)
    (unpublished : ¬Published matching events occurrence)
    (cancelled : TaskCancelled work matching events failures producer)
    : TaskCancelled work matching events failures occurrence := by
  obtain ⟨cut, member, reached, cause⟩ := cancelled
  refine ⟨cut, member, reached,
    Causality.TaskCancelled.producerCancelled ⟨owners, payload, known⟩ ?_ cause⟩
  rintro ⟨index, event, selected, value, same⟩
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have inside : index < cut := by simp only [List.length_take] at bound; omega
  exact unpublished ⟨index, event,
    (List.getElem?_take_of_lt inside).symm.trans selected, value, same⟩

/-- Publication readiness ignores failure cuts beyond the observed boundary.
Witness: cancellation cutoff invariance; publication dependencies are unchanged.
-/
theorem canPublish_filter {work matching events failures occurrence producer bound}
    (within : events.length ≤ bound)
    : CanPublish work matching events (failures.filter (fun entry => entry.1 ≤ bound))
        occurrence producer
      = CanPublish work matching events failures occurrence producer := by
  simp only [CanPublish, taskCancelled_filter within]

/-- Node accounting ignores failure cuts beyond the observed boundary.
Witness: cancellation cutoff invariance for each contributing task.
-/
theorem nodeAccounted_filter {work matching events failures ref bound}
    (within : events.length ≤ bound)
    : NodeAccounted work matching events
        (failures.filter (fun entry => entry.1 ≤ bound)) ref
      = NodeAccounted work matching events failures ref := by
  simp only [NodeAccounted, TaskAccounted, taskCancelled_filter within]

/-- Effective owner selection ignores failures beyond the observed boundary.
Witness: node-failure cutoff invariance for every competing contributor.
-/
theorem owner_filter {work initial matching events failures owners node bound}
    (within : events.length ≤ bound)
    : PublicationOwner work initial matching events
        (failures.filter (fun entry => entry.1 ≤ bound)) owners node
      = PublicationOwner work initial matching events failures owners node := by
  simp only [PublicationOwner, HealthyOpenOwner, nodeFailed_filter within]

end GraphQL.IncrementalDelivery.WorkQueueSemantics
