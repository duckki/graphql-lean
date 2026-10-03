import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.HistoryExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.PublicationOrder

/-! Actual reachable failures can extend history evidence and produce notifications. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Causal evidence is monotone
-----------------------------------------------------------------------------------------

/-- Additional failures preserve a node failure at a fixed publication snapshot.
Witness: mutual causal induction, retaining every publication exclusion.
-/
theorem Causality.NodeFailed.mono {work failed more published ref}
    (failure : Causality.NodeFailed work failed published ref)
    (included : failed.Subset more)
    : Causality.NodeFailed work more published ref := by
  induction failure
    using Causality.NodeFailed.rec
      (motive_2 :=
        fun occurrence _ =>
          Causality.TaskCancelled work more published occurrence) with
  | task known owner member =>
      exact Causality.NodeFailed.task known owner (included member)
  | groupDependency known member _ ih =>
      exact Causality.NodeFailed.groupDependency known member ih
  | streamDependencies known nonempty _ ih =>
      exact Causality.NodeFailed.streamDependencies known nonempty ih
  | producers known noRoot unpublished _ ih =>
      exact Causality.NodeFailed.producers known noRoot unpublished
        (fun producerOccurrence known absent =>
          ih producerOccurrence known (fun member => absent (included member)))
  | owners known unpublished nonempty _ ih =>
      exact Causality.TaskCancelled.owners known unpublished nonempty ih
  | producerFailed known unpublished member =>
      exact Causality.TaskCancelled.producerFailed known unpublished (included member)
  | producerCancelled known unpublished _ ih =>
      exact Causality.TaskCancelled.producerCancelled known unpublished ih

/-- Additional failures preserve cancellation at a fixed publication snapshot.
Witness: mutual causal induction with the same publication exclusions.
-/
theorem Causality.TaskCancelled.mono {work failed more published occurrence}
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    (included : failed.Subset more)
    : Causality.TaskCancelled work more published occurrence := by
  induction cancelled
    using Causality.TaskCancelled.rec
      (motive_1 := fun ref _ => Causality.NodeFailed work more published ref) with
  | task known owner member =>
      exact Causality.NodeFailed.task known owner (included member)
  | groupDependency known member _ ih =>
      exact Causality.NodeFailed.groupDependency known member ih
  | streamDependencies known nonempty _ ih =>
      exact Causality.NodeFailed.streamDependencies known nonempty ih
  | producers known noRoot unpublished _ ih =>
      exact Causality.NodeFailed.producers known noRoot unpublished
        (fun producerOccurrence known absent =>
          ih producerOccurrence known (fun member => absent (included member)))
  | owners known unpublished nonempty _ ih =>
      exact Causality.TaskCancelled.owners known unpublished nonempty ih
  | producerFailed known unpublished member =>
      exact Causality.TaskCancelled.producerFailed known unpublished (included member)
  | producerCancelled known unpublished _ ih =>
      exact Causality.TaskCancelled.producerCancelled known unpublished ih

/-- Moving a causal snapshot forward preserves node failures when failed and cancelled
tasks cannot publish in between. Witness: mutual induction through every causal rule.
-/
theorem Causality.NodeFailed.advance {work failed more published next ref}
    (failure : Causality.NodeFailed work failed published ref)
    (included : failed.Subset more)
    (failedUnpublished : ∀ occurrence ∈ failed, ¬next occurrence)
    (cancelledUnpublished
      : ∀ occurrence,
          Causality.TaskCancelled work failed published occurrence → ¬next occurrence)
    : Causality.NodeFailed work more next ref := by
  induction failure
    using Causality.NodeFailed.rec
      (motive_2 :=
        fun occurrence _ => Causality.TaskCancelled work more next occurrence) with
  | task known owner member =>
      exact Causality.NodeFailed.task known owner (included member)
  | groupDependency known dependency _ ih =>
      exact Causality.NodeFailed.groupDependency known dependency ih
  | streamDependencies known nonempty _ ih =>
      exact Causality.NodeFailed.streamDependencies known nonempty ih
  | producers known noRoot unpublished cancelled ih =>
      refine Causality.NodeFailed.producers known noRoot ?_ ?_
      · intro producer located
        by_cases member : producer ∈ failed
        · exact failedUnpublished producer member
        · exact (ih producer located member).unpublished
      · intro producer located absent
        exact ih producer located (fun member => absent (included member))
  | owners known unpublished nonempty failures ih =>
      exact Causality.TaskCancelled.owners known
        (cancelledUnpublished _ (.owners known unpublished nonempty failures))
        nonempty ih
  | producerFailed known unpublished member =>
      exact Causality.TaskCancelled.producerFailed known
        (cancelledUnpublished _ (.producerFailed known unpublished member))
        (included member)
  | producerCancelled known unpublished cancelled ih =>
      exact Causality.TaskCancelled.producerCancelled known
        (cancelledUnpublished _ (.producerCancelled known unpublished cancelled)) ih

/-- Moving a causal snapshot forward preserves cancellation if no affected task revives.
Witness: the same mutual induction, retaining exclusions from the observed history.
-/
theorem Causality.TaskCancelled.advance {work failed more published next occurrence}
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    (included : failed.Subset more)
    (failedUnpublished : ∀ occurrence ∈ failed, ¬next occurrence)
    (cancelledUnpublished
      : ∀ occurrence,
          Causality.TaskCancelled work failed published occurrence → ¬next occurrence)
    : Causality.TaskCancelled work more next occurrence := by
  induction cancelled
    using Causality.TaskCancelled.rec
      (motive_1 := fun ref _ => Causality.NodeFailed work more next ref) with
  | task known owner member =>
      exact Causality.NodeFailed.task known owner (included member)
  | groupDependency known dependency _ ih =>
      exact Causality.NodeFailed.groupDependency known dependency ih
  | streamDependencies known nonempty _ ih =>
      exact Causality.NodeFailed.streamDependencies known nonempty ih
  | producers known noRoot unpublished cancelled ih =>
      refine Causality.NodeFailed.producers known noRoot ?_ ?_
      · intro producer located
        by_cases member : producer ∈ failed
        · exact failedUnpublished producer member
        · exact (ih producer located member).unpublished
      · intro producer located absent
        exact ih producer located (fun member => absent (included member))
  | owners known unpublished nonempty failures ih =>
      exact Causality.TaskCancelled.owners known
        (cancelledUnpublished _ (.owners known unpublished nonempty failures))
        nonempty ih
  | producerFailed known unpublished member =>
      exact Causality.TaskCancelled.producerFailed known
        (cancelledUnpublished _ (.producerFailed known unpublished member))
        (included member)
  | producerCancelled known unpublished cancelled ih =>
      exact Causality.TaskCancelled.producerCancelled known
        (cancelledUnpublished _ (.producerCancelled known unpublished cancelled)) ih

/-- Historical node failures remain derivable at the current admitted snapshot.
Witness: advance their original cut using the absence of failed/cancelled publications.
-/
theorem Explains.nodeFailed_snapshot {work groups streams events matching failures ref}
    (explained : Explains work groups streams events matching failures)
    (failure : NodeFailed work matching events failures ref)
    : Causality.NodeFailed work (failedBefore failures events.length)
        (Published matching events) ref := by
  obtain ⟨cut, member, reached, cause⟩ := failure
  apply cause.advance
  · intro occurrence selected
    obtain ⟨entry, kept, same⟩ := List.mem_map.mp selected
    obtain ⟨inCuts, bounded⟩ := List.mem_filter.mp kept
    rw [← same]
    exact mem_failedBefore inCuts (Nat.le_trans (by simpa using bounded) reached)
  · exact fun _ failed => explained.failed_unpublished failed
  · exact fun _ cancelled =>
      explained.cancelled_unpublished ⟨cut, member, reached, cancelled⟩

/-- Historical cancellation remains derivable at the current admitted snapshot.
Witness: advance the same reached cut, using exclusion of all later revivals.
-/
theorem Explains.taskCancelled_snapshot
    {work groups streams events matching failures occurrence}
    (explained : Explains work groups streams events matching failures)
    (cancelled : TaskCancelled work matching events failures occurrence)
    : Causality.TaskCancelled work (failedBefore failures events.length)
        (Published matching events) occurrence := by
  obtain ⟨cut, member, reached, cause⟩ := cancelled
  apply cause.advance
  · intro occurrence selected
    obtain ⟨entry, kept, same⟩ := List.mem_map.mp selected
    obtain ⟨inCuts, bounded⟩ := List.mem_filter.mp kept
    rw [← same]
    exact mem_failedBefore inCuts (Nat.le_trans (by simpa using bounded) reached)
  · exact fun _ failed => explained.failed_unpublished failed
  · exact fun _ cancelled =>
      explained.cancelled_unpublished ⟨cut, member, reached, cancelled⟩

/-- The last licensed cut sees every recorded failure and lies inside the history.
Witness: ordered evidence at the final entry of the nonempty cut list.
-/
theorem FailureWitness.last_cut {work initial matching events failures}
    (witness : FailureWitness work initial matching events failures)
    (nonempty : failures ≠ [])
    : ∃ cut,
        cut ∈ failures.map Prod.fst
        ∧ cut ≤ events.length
        ∧ failedBefore failures cut = failedBefore failures events.length := by
  rcases List.eq_nil_or_concat failures with empty | ⟨before, ⟨cut, occurrence⟩, equal⟩
  · exact False.elim (nonempty empty)
  simp only [List.concat_eq_append] at equal
  have facts := witness before cut occurrence [] equal
  refine ⟨cut, List.mem_map.mpr ⟨(cut, occurrence), by simp [equal], rfl⟩, facts.1, ?_⟩
  rw [witness.failedBefore_eq (Nat.le_refl _)]
  unfold failedBefore
  congr 1
  apply List.filter_eq_self.mpr
  intro entry member
  rw [equal] at member
  rcases List.mem_append.mp member with prior | last
  · simpa using facts.2.1 entry prior
  · have same : entry = (cut, occurrence) := List.mem_singleton.mp last
    simp [same]

/-- A current-snapshot node failure has a historical cut witness.
Witness: move it back to the last recorded cut; fewer publications cannot obstruct
its causal derivation, and every failed occurrence is still visible there.
-/
theorem Explains.snapshot_nodeFailed {work groups streams events matching failures ref}
    (explained : Explains work groups streams events matching failures)
    (failure
      : Causality.NodeFailed work (failedBefore failures events.length)
          (Published matching events) ref)
    : NodeFailed work matching events failures ref := by
  have nonempty : failures ≠ [] := by
    intro empty
    exact failure.nonempty (by simp [empty, failedBefore])
  obtain ⟨cut, member, reached, same⟩ := explained.2.1.last_cut nonempty
  refine ⟨cut, member, reached, ?_⟩
  rw [same]
  apply failure.advance (List.Subset.refl _)
  · intro occurrence failed published
    apply explained.failed_unpublished failed
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  · intro occurrence cancelled published
    apply cancelled.unpublished
    simpa only [List.take_append_drop] using published.append (events.drop cut)

/-- Current-snapshot cancellation also has a historical cut witness.
Witness: the last cut supplies the same failures and a smaller publication snapshot.
-/
theorem Explains.snapshot_taskCancelled
    {work groups streams events matching failures occurrence}
    (explained : Explains work groups streams events matching failures)
    (cancelled
      : Causality.TaskCancelled work (failedBefore failures events.length)
          (Published matching events) occurrence)
    : TaskCancelled work matching events failures occurrence := by
  have nonempty : failures ≠ [] := by
    intro empty
    exact cancelled.nonempty (by simp [empty, failedBefore])
  obtain ⟨cut, member, reached, same⟩ := explained.2.1.last_cut nonempty
  refine ⟨cut, member, reached, ?_⟩
  rw [same]
  apply cancelled.advance (List.Subset.refl _)
  · intro occurrence failed published
    apply explained.failed_unpublished failed
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  · intro occurrence cancelled published
    apply cancelled.unpublished
    simpa only [List.take_append_drop] using published.append (events.drop cut)

/-- Historical and current-snapshot node failure agree on an admitted history.
Witness: forward no-revival transport and backward transport to the last licensed cut.
-/
theorem Explains.nodeFailed_iff_snapshot
    {work groups streams events matching failures ref}
    (explained : Explains work groups streams events matching failures)
    : NodeFailed work matching events failures ref
      ↔ Causality.NodeFailed work (failedBefore failures events.length)
          (Published matching events) ref :=
  ⟨explained.nodeFailed_snapshot, explained.snapshot_nodeFailed⟩

/-- Historical and current-snapshot cancellation agree on an admitted history.
Witness: the same two cut-preserving transports, without a new scheduler premise.
-/
theorem Explains.taskCancelled_iff_snapshot
    {work groups streams events matching failures occurrence}
    (explained : Explains work groups streams events matching failures)
    : TaskCancelled work matching events failures occurrence
      ↔ Causality.TaskCancelled work (failedBefore failures events.length)
          (Published matching events) occurrence :=
  ⟨explained.taskCancelled_snapshot, explained.snapshot_taskCancelled⟩

/-- More recorded cuts retain all failures visible at a given boundary.
Witness: preserve each filtered entry and its occurrence projection.
-/
theorem failedBefore_mono {failures more : FailureCuts} (included : failures.Subset more)
    (cut : Nat)
    : (failedBefore failures cut).Subset (failedBefore more cut) := by
  intro occurrence member
  obtain ⟨entry, kept, rfl⟩ := List.mem_map.mp member
  obtain ⟨member, bounded⟩ := List.mem_filter.mp kept
  exact List.mem_map.mpr ⟨entry,
    List.mem_filter.mpr ⟨included member, bounded⟩, rfl⟩

/-- Additional recorded cuts preserve an earlier node failure.
Witness: retain its original cut and extend only that cut's failed occurrences.
-/
theorem NodeFailed.mono {work matching events failures more ref}
    (failure : NodeFailed work matching events failures ref)
    (included : failures.Subset more)
    : NodeFailed work matching events more ref := by
  obtain ⟨cut, member, reached, cause⟩ := failure
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
  exact ⟨entry.1, List.mem_map.mpr ⟨entry, included entryMember, rfl⟩, reached,
    cause.mono (failedBefore_mono included _)⟩

/-- Additional recorded cuts preserve cancellation at its original snapshot.
Witness: retain the reached cut and apply snapshot causal monotonicity.
-/
theorem TaskCancelled.mono {work matching events failures more occurrence}
    (cancelled : TaskCancelled work matching events failures occurrence)
    (included : failures.Subset more)
    : TaskCancelled work matching events more occurrence := by
  obtain ⟨cut, member, reached, cause⟩ := cancelled
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
  exact ⟨entry.1, List.mem_map.mpr ⟨entry, included entryMember, rfl⟩, reached,
    cause.mono (failedBefore_mono included _)⟩

/-- A recorded failure cancels its own nonempty-owned, unpublished task.
Witness: at that failure cut the task fails each contributing owner.
-/
theorem TaskCancelled.of_recorded
    {work matching events failures occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload) (nonempty : owners ≠ [])
    (unpublished : ¬Published matching events occurrence)
    (member : occurrence ∈ failedBefore failures events.length)
    : TaskCancelled work matching events failures occurrence := by
  obtain ⟨⟨cut, task⟩, kept, same⟩ := List.mem_map.mp member
  obtain ⟨member, bounded⟩ := List.mem_filter.mp kept
  dsimp only at same
  subst task
  refine ⟨
    cut,
    List.mem_map.mpr ⟨(cut, occurrence), member, rfl⟩,
    by simpa using bounded,
    ?_
  ⟩
  refine Causality.TaskCancelled.owners ⟨producer, payload, known⟩ ?_ nonempty ?_
  · intro published
    apply unpublished
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  · intro ref owner
    exact Causality.NodeFailed.task ⟨producer, payload, known⟩ owner
      (mem_failedBefore member (Nat.le_refl _))

/-- More failure evidence preserves task accounting. Witness: causal monotonicity for
cancelled tasks, with already published tasks unchanged.
-/
theorem TaskAccounted.more_failures {work matching events failed more occurrence}
    (accounted : TaskAccounted work matching events failed occurrence)
    (included : failed.Subset more)
    : TaskAccounted work matching events more occurrence :=
  accounted.imp_left (fun cancelled => cancelled.mono included)

-----------------------------------------------------------------------------------------
-- Recording a failure at the current output boundary
-----------------------------------------------------------------------------------------

/-- A selected entry of a list extended by one element is either the new last element
or an original entry. Witness: induction on the selected entry's prefix.
-/
private theorem split_snoc {α : Type} {original before after : List α} {entry last : α}
    (same : original ++ [last] = before ++ entry :: after)
    : (original = before ∧ entry = last ∧ after = [])
      ∨ ∃ rest, original = before ++ entry :: rest ∧ after = rest ++ [last] := by
  induction before generalizing original with
  | nil =>
      cases original with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at same
          exact Or.inl ⟨rfl, same.1.symm, same.2.symm⟩
      | cons head rest =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at same
          exact Or.inr ⟨rest, by simp [same.1], same.2.symm⟩
  | cons head before ih =>
      cases original with
      | nil =>
          have lengths := congrArg List.length same
          simp only [List.nil_append, List.length_cons, List.length_nil,
            List.length_append] at lengths
          omega
      | cons first rest =>
          simp only [List.cons_append, List.cons.injEq] at same
          obtain ⟨rfl, same⟩ := same
          rcases ih same with ⟨rfl, equal, rfl⟩ | ⟨tail, equal, remaining⟩
          · exact Or.inl ⟨rfl, equal, rfl⟩
          · exact Or.inr ⟨tail, by simp only [equal, List.cons_append], remaining⟩

/-- A reachable failing task with an open owner can be recorded at the current boundary,
provided it has not already been cancelled. Witness: append one fresh ordered failure
cut; every earlier failure keeps exactly its previous causal evidence.
-/
theorem FailureWitness.record
    {work initial matching events failures occurrence owners producer payload}
    (witness : FailureWitness work initial matching events failures)
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true) (reachable : Reachable work occurrence)
    (opened : ∃ ref ∈ owners, Open initial events ref)
    (active : ¬TaskCancelled work matching events failures occurrence)
    : FailureWitness work initial matching events
        (failures ++ [(events.length, occurrence)]) := by
  intro before cut failed after same
  rcases split_snoc same with ⟨rfl, equal, rfl⟩ | ⟨rest, original, _⟩
  · cases equal
    obtain ⟨ref, owner, announced, _⟩ := opened
    exact ⟨Nat.le_refl _, fun entry member => witness.cut_le member,
      ⟨owners, producer, payload, known, fails, reachable,
        ref, owner, by simpa using announced⟩,
      by simpa using active⟩
  · exact witness before cut failed rest original

/-- A newly recorded final-boundary failure is invisible at every earlier output index.
Witness: its cut is strictly larger than the index selected by an existing event.
-/
theorem failedBefore_record_before (failures : FailureCuts) (occurrence : Occurrence)
    {cut index : Nat} (earlier : index < cut)
    : failedBefore (failures ++ [(cut, occurrence)]) index
      = failedBefore failures index := by
  simp [failedBefore, List.filter_append, Nat.not_le.mpr earlier]

/-- At the current boundary all original failures and the newly recorded failure are
visible. Witness: the old witness bounds every previous cut.
-/
theorem FailureWitness.failedBefore_record {work initial matching events failures}
    (witness : FailureWitness work initial matching events failures)
    (occurrence : Occurrence)
    : failedBefore (failures ++ [(events.length, occurrence)]) events.length
      = failures.map Prod.snd ++ [occurrence] := by
  have previous := witness.failedBefore_eq (Nat.le_refl _)
  simp only [failedBefore] at previous
  simpa [failedBefore, List.filter_append]
    using congrArg (fun failed => failed ++ [occurrence]) previous

/-- Recording a failure at the current boundary preserves every already admitted event.
Witness: append the justified failure cut and keep the old evidence at earlier indices.
-/
theorem Explains.record_failure
    {work groups streams events matching failures occurrence owners producer payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true) (reachable : Reachable work occurrence)
    (opened : ∃ ref ∈ owners, Open ((groups ++ streams).map DeliveryNode.ref) events ref)
    (active : ¬TaskCancelled work matching events failures occurrence)
    : Explains work groups streams events matching
        (failures ++ [(events.length, occurrence)]) := by
  refine ⟨explained.1,
    explained.2.1.record known fails reachable opened active, ?_⟩
  intro index event selected
  have earlier : (events.take index).length < events.length := by
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    simp only [List.length_take]; omega
  simpa only [EventAllowed, List.filter_append, List.filter_cons,
    show decide (events.length ≤ (events.take index).length) = false from
      decide_eq_false (Nat.not_le.mpr earlier), Bool.false_eq_true, ↓reduceIte,
    List.filter_nil, List.append_nil]
    using explained.2.2 index event selected

/-- Any recordable failure can make observable progress by closing one open contributing
owner. Witness: append its actual failure cut, choose a supported open descriptor, and
emit its counted failure completion. The error count includes the new task's failure.
-/
theorem Explains.failure_step
    {work groups streams events matching failures occurrence owners producer payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true) (reachable : Reachable work occurrence)
    (opened : ∃ ref ∈ owners, Open ((groups ++ streams).map DeliveryNode.ref) events ref)
    (active : ¬TaskCancelled work matching events failures occurrence)
    : ∃ node errors event,
        node.ref ∈ owners
        ∧ (event = .groupFailure node errors ∨ event = .streamFailure node errors)
        ∧ payload.failure.getD 0 ≤ errors
        ∧ Explains work groups streams (events ++ [event]) matching
            (failures ++ [(events.length, occurrence)]) := by
  have recorded := explained.record_failure known fails reachable opened active
  obtain ⟨ref, owner, openRef⟩ := opened
  obtain ⟨node, kind, dependencies, birth, nodeKnown, same⟩ :=
    explained.noticeFacts.supported ref openRef.1
  have member : occurrence ∈ failedBefore
      (failures ++ [(events.length, occurrence)]) events.length := by
    simp [failedBefore]
  have failed : NodeFailed work matching events
      (failures ++ [(events.length, occurrence)]) node.ref :=
    .task known (same ▸ owner) member
  have knownFailures := recorded.2.1.known
  rw [← recorded.2.1.failedBefore_eq (Nat.le_refl _)] at knownFailures
  obtain ⟨errors, counts⟩ := NodeErrors.exists knownFailures node.ref
  have includes := counts.contribution_le member known (same ▸ owner)
  have nodeOpen : Open ((groups ++ streams).map DeliveryNode.ref) events node.ref :=
    same ▸ openRef
  have finish {event}
      (allowed
        : EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
            events (failures ++ [(events.length, occurrence)]) event)
      : Explains work groups streams (events ++ [event]) matching
          (failures ++ [(events.length, occurrence)]) :=
    recorded.append_event allowed
  cases kind with
  | group =>
      refine ⟨node, errors, .groupFailure node errors, same ▸ owner, Or.inl rfl,
        includes, finish ?_⟩
      simpa only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
        failedBefore_filter _ (Nat.le_refl _)]
        using And.intro ⟨dependencies, birth, nodeKnown⟩ ⟨nodeOpen, failed, counts⟩
  | stream =>
      refine ⟨node, errors, .streamFailure node errors, same ▸ owner, Or.inr rfl,
        includes, finish ?_⟩
      simpa only [EventAllowed, nodeFailed_filter (Nat.le_refl _),
        failedBefore_filter _ (Nat.le_refl _)]
        using And.intro ⟨dependencies, birth, nodeKnown⟩ ⟨nodeOpen, failed, counts⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
