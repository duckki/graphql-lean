import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.HistoryExtension

/-! Actual reachable failures can extend history evidence and produce notifications. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Causal evidence is monotone
-----------------------------------------------------------------------------------------

/-- Additional actual failures preserve an already derived node failure. Witness: mutual
causal induction; a newly failed producer no longer needs a cancellation derivation.
-/
theorem NodeFailed.mono {work failed more key} (failure : NodeFailed work failed key)
    (included : failed.Subset more)
    : NodeFailed work more key := by
  induction failure
    using Causality.NodeFailed.rec
      (motive_2 := fun occurrence _ => TaskCancelled work more occurrence) with
  | task known owner member =>
      exact Causality.NodeFailed.task known owner (included member)
  | groupDependency known member _ ih =>
      exact Causality.NodeFailed.groupDependency known member ih
  | streamDependencies known nonempty _ ih =>
      exact Causality.NodeFailed.streamDependencies known nonempty ih
  | producers known noRoot _ ih =>
      exact Causality.NodeFailed.producers known noRoot
        (fun producerOccurrence known absent =>
          ih producerOccurrence known (fun member => absent (included member)))
  | owners known nonempty _ ih => exact Causality.TaskCancelled.owners known nonempty ih
  | producerFailed known member =>
      exact Causality.TaskCancelled.producerFailed known (included member)
  | producerCancelled known _ ih =>
      exact Causality.TaskCancelled.producerCancelled known ih

/-- Additional actual failures preserve cancellation. Witness: the same mutual causal
induction; no task is revived by extending the failure evidence.
-/
theorem TaskCancelled.mono {work failed more occurrence}
    (cancelled : TaskCancelled work failed occurrence) (included : failed.Subset more)
    : TaskCancelled work more occurrence := by
  induction cancelled
    using Causality.TaskCancelled.rec
      (motive_1 := fun key _ => NodeFailed work more key) with
  | task known owner member =>
      exact Causality.NodeFailed.task known owner (included member)
  | groupDependency known member _ ih =>
      exact Causality.NodeFailed.groupDependency known member ih
  | streamDependencies known nonempty _ ih =>
      exact Causality.NodeFailed.streamDependencies known nonempty ih
  | producers known noRoot _ ih =>
      exact Causality.NodeFailed.producers known noRoot
        (fun producerOccurrence known absent =>
          ih producerOccurrence known (fun member => absent (included member)))
  | owners known nonempty _ ih => exact Causality.TaskCancelled.owners known nonempty ih
  | producerFailed known member =>
      exact Causality.TaskCancelled.producerFailed known (included member)
  | producerCancelled known _ ih =>
      exact Causality.TaskCancelled.producerCancelled known ih

/-- A recorded failure accounts for its own nonempty-owned task by cancellation.
Witness: that failure fails every contributing owner.
-/
theorem TaskCancelled.of_recorded {work failed occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload) (nonempty : owners ≠ [])
    (member : occurrence ∈ failed)
    : TaskCancelled work failed occurrence :=
  .owners known nonempty (fun _ owner => .task known owner member)

/-- More failure evidence preserves task accounting. Witness: causal monotonicity for
cancelled tasks, with already published tasks unchanged.
-/
theorem Accounted.more_failures {work matching events failed more occurrence}
    (accounted : Accounted work matching events failed occurrence)
    (included : failed.Subset more)
    : Accounted work matching events more occurrence :=
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
    {work initial events failures occurrence owners producer payload}
    (witness : FailureWitness work initial events failures)
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true) (reachable : Reachable work occurrence)
    (opened : ∃ key ∈ owners, Open initial events key)
    (active : ¬TaskCancelled work (failures.map Prod.snd) occurrence)
    : FailureWitness work initial events (failures ++ [(events.length, occurrence)]) := by
  intro before cut failed after same
  rcases split_snoc same with ⟨rfl, equal, rfl⟩ | ⟨rest, original, _⟩
  · cases equal
    exact ⟨Nat.le_refl _, fun entry member => witness.cut_le member,
      ⟨owners, producer, payload, known, fails, reachable, by simpa using opened⟩,
      active⟩
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
theorem FailureWitness.failedBefore_record {work initial events failures}
    (witness : FailureWitness work initial events failures) (occurrence : Occurrence)
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
    (opened : ∃ key ∈ owners, Open ((groups ++ streams).map DeliveryNode.key) events key)
    (active : ¬TaskCancelled work (failures.map Prod.snd) occurrence)
    : Explains work groups streams events matching
        (failures ++ [(events.length, occurrence)]) := by
  refine ⟨explained.1,
    explained.2.1.record known fails reachable opened active, ?_⟩
  intro index event selected
  rw [failedBefore_record_before failures occurrence
    (List.getElem?_eq_some_iff.mp selected).1]
  exact explained.2.2 index event selected

/-- Any recordable failure can make observable progress by closing one open contributing
owner. Witness: append its actual failure cut, choose a supported open descriptor, and
emit its counted failure completion. The error count includes the new task's failure.
-/
theorem Explains.failure_step
    {work groups streams events matching failures occurrence owners producer payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true) (reachable : Reachable work occurrence)
    (opened : ∃ key ∈ owners, Open ((groups ++ streams).map DeliveryNode.key) events key)
    (active : ¬TaskCancelled work (failures.map Prod.snd) occurrence)
    : ∃ node errors event,
        node.key ∈ owners
        ∧ (event = .groupFailure node errors ∨ event = .streamFailure node errors)
        ∧ payload.failure.getD 0 ≤ errors
        ∧ Explains work groups streams (events ++ [event]) matching
            (failures ++ [(events.length, occurrence)]) := by
  have recorded := explained.record_failure known fails reachable opened active
  obtain ⟨key, owner, openKey⟩ := opened
  obtain ⟨node, kind, dependencies, birth, nodeKnown, same⟩ :=
    explained.noticeFacts.supported key openKey.1
  have member : occurrence ∈ (failures ++ [(events.length, occurrence)]).map Prod.snd := by
    simp
  have failed : NodeFailed work
      ((failures ++ [(events.length, occurrence)]).map Prod.snd) node.key :=
    .task known (same ▸ owner) member
  obtain ⟨errors, counts⟩ := NodeErrors.exists recorded.2.1.known node.key
  have includes := counts.contribution_le member known (same ▸ owner)
  have nodeOpen : Open ((groups ++ streams).map DeliveryNode.key) events node.key :=
    same ▸ openKey
  have finish {event}
      (allowed
        : EventAllowed work ((groups ++ streams).map DeliveryNode.key) matching
            events ((failures ++ [(events.length, occurrence)]).map Prod.snd) event)
      : Explains work groups streams (events ++ [event]) matching
          (failures ++ [(events.length, occurrence)]) :=
    recorded.append_event
      (by simpa only [recorded.2.1.failedBefore_eq (Nat.le_refl _)] using allowed)
  cases kind with
  | group => exact ⟨node, errors, .groupFailure node errors, same ▸ owner, Or.inl rfl,
      includes, finish ⟨⟨dependencies, birth, nodeKnown⟩, nodeOpen, failed, counts⟩⟩
  | stream => exact ⟨node, errors, .streamFailure node errors, same ▸ owner, Or.inr rfl,
      includes, finish ⟨⟨dependencies, birth, nodeKnown⟩, nodeOpen, failed, counts⟩⟩

end GraphQL.IncrementalDelivery.WorkScheduler
