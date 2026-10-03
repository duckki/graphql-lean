import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCausalHealth

/-! Stream admission and root licensing survive interleaved object-failure cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Partitioning a witness preserves exact cut positions and visible multiplicities
-----------------------------------------------------------------------------------------

/-- Permuting cuts preserves the visible failure inventory at every output boundary.
Witness: filter at the same cut position, then project occurrences. This does not move
any cut or claim that arbitrary failure-witness order is admissible.
-/
theorem failedBefore_perm {before after : FailureCuts} (same : before.Perm after)
    (index : Nat)
    : (failedBefore before index).Perm (failedBefore after index) :=
  (same.filter _).map Prod.snd

/-- A mixed list's visible failures are the two partitions' visible failures interleaved.
Witness: the position-preserving permutation and distribution of filtering over append.
-/
theorem failedBefore_partition {failures streams objects : FailureCuts}
    (partition : failures.Perm (streams ++ objects)) (index : Nat)
    : (failedBefore failures index).Perm
        (failedBefore streams index ++ failedBefore objects index) := by
  simpa only [failedBefore, List.filter_append, List.map_append]
    using failedBefore_perm partition index

/-- One stream-failure output position has only one retained occurrence label.
Witness: strict cut ordering makes the position projection duplicate-free; equal
projected positions therefore identify the same list entry.
-/
theorem StreamFailureCuts.unique_at {work events failures first second}
    (cuts : StreamFailureCuts work events failures)
    (left : first ∈ failures) (right : second ∈ failures) (same : first.1 = second.1)
    : first = second := by
  have unique : (failures.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (cuts.ordered.imp (fun less => Nat.ne_of_lt less))
  obtain ⟨i, ib, atI⟩ := List.mem_iff_getElem.mp left
  obtain ⟨j, jb, atJ⟩ := List.mem_iff_getElem.mp right
  have equal := unique.eq_of_getElem_eq
    (by simpa only [List.length_map] using ib)
    (by simpa only [List.length_map] using jb)
    (by simpa only [List.getElem_map, atI, atJ] using same)
  subst j
  exact atI.symm.trans atJ

-----------------------------------------------------------------------------------------
-- Stream failure events retain their exact meaning under the full cut list
-----------------------------------------------------------------------------------------

/-- Interleaved object cuts do not alter the errors reported by a stream failure.
Witness: partition the visible inventory at this exact output position, assign zero
to generated object-task contributions, and retain the original failure multiplicity.
Licensing either partition is a separate obligation.
-/
theorem StreamFailureCuts.nodeErrors_mixed
    {work events streamCuts objectCuts failures index stream errors}
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    : NodeErrors work (failedBefore failures index) stream.ref errors := by
  have counts := cuts.nodeErrors_with_objects ordered generated atEvent
    (failedBefore objectCuts index) (by
      intro occurrence member
      obtain ⟨entry, retained, same⟩ := List.mem_map.mp member
      exact same ▸ objects entry (List.mem_filter.mp retained).1)
  exact nodeErrors_of_perm counts (failedBefore_partition partition index).symm

/-- A stream-failure completion is admitted under the full mixed failure inventory.
Witness: the current stream cut remains present, so it still causes historical failure;
the partitioned count theorem and independently proved Open supply the other clauses.
Unlike the stream-only bridge, this does not discard object failure cuts.
-/
theorem StreamFailureCuts.eventAllowed_mixed
    {work events streamCuts objectCuts failures index stream errors initial matching}
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    (opened : Open initial (events.take index) stream.ref)
    : EventAllowed work initial matching (events.take index) failures
        (.streamFailure stream errors) := by
  obtain ⟨occurrence, member⟩ := cuts.covers atEvent
  obtain ⟨node, count, producer, selected, known⟩ := cuts.2 _ member
  obtain ⟨sameNode, sameCount⟩ :=
    Execution.WorkQueueEvent.streamFailure.inj (Option.some.inj (selected.symm.trans atEvent))
  subst node count
  obtain ⟨dependencies, located⟩ := (itemTask_owner_nodeAt known).2
  have included : (index, occurrence) ∈ failures :=
    partition.mem_iff.mpr (List.mem_append_left _ member)
  have length : (events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atEvent).1)
  have failed : NodeFailed work matching (events.take index) failures stream.ref :=
    NodeFailed.task known List.mem_cons_self
      (length.symm ▸ mem_failedBefore included (Nat.le_refl index))
  simp only [EventAllowed]
  rw [nodeFailed_filter (Nat.le_refl _), failedBefore_filter _ (Nat.le_refl _), length]
  exact ⟨⟨dependencies, producer, located⟩, opened, failed,
    cuts.nodeErrors_mixed partition objects generated ordered atEvent⟩

-----------------------------------------------------------------------------------------
-- Object failures cannot directly cancel root-stream items
-----------------------------------------------------------------------------------------

/-- A nonfailure stream action has no contributing failure in either cut partition.
Witness: source closure order excludes stream cuts, and generated group/stream role
separation excludes every object cut. Positions and the full list are unchanged.
-/
theorem StreamFailureCuts.no_failure_at_action_mixed
    {work events streamCuts objectCuts failures index event stream closing occurrence
      owners dependencies producer}
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (located : NodeAt work stream .stream dependencies producer)
    (atEvent : events[index]? = some event)
    (action : streamAction event = some (stream.ref, closing))
    (notFailure : ∀ node errors, event ≠ .streamFailure node errors)
    (known : TaskHasOwners work occurrence owners) (owner : stream.ref ∈ owners)
    : occurrence ∉ failedBefore failures index := by
  intro failed
  have member := (failedBefore_partition partition index).mem_iff.mp failed
  rcases List.mem_append.mp member with fromStream | fromObject
  · exact cuts.no_failure_at_action ordered atEvent action notFailure known owner fromStream
  · obtain ⟨entry, retained, same⟩ := List.mem_map.mp fromObject
    obtain ⟨otherOwners, parent, path, errors, task⟩ :=
      objects entry (List.mem_filter.mp retained).1
    rw [same] at task
    obtain ⟨birth, payload, descriptor⟩ := known
    exact generated.objectFailure_not_streamOwner located task ((descriptor.unique task).1 ▸ owner)

/-- Root-stream health survives the complete interleaved object/stream cut inventory.
Witness: root failure is necessarily direct, and neither partition can contribute a
visible failure to a stream that is still publishing or completing successfully.
-/
theorem StreamFailureCuts.rootStream_healthy_mixed
    {work events streamCuts objectCuts failures index event stream closing matching}
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (root : NodeAt work stream .stream [] none)
    (atEvent : events[index]? = some event)
    (action : streamAction event = some (stream.ref, closing))
    (notFailure : ∀ node errors, event ≠ .streamFailure node errors)
    : ¬NodeFailed work matching (events.take index) failures stream.ref := by
  intro failed
  obtain ⟨occurrence, owners, known, owner, member⟩ :=
    (generated.rootStream_nodeFailed_iff root).mp failed
  have length : (events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atEvent).1)
  rw [length] at member
  exact cuts.no_failure_at_action_mixed partition objects generated ordered root
    atEvent action notFailure known owner member

/-- A root-stream failure is uncancelled by the preceding portion of a mixed cut list.
Witness: prior cancellation would fail its sole root owner. Object cuts cannot own it;
an earlier stream cut would close that ref already. Same-position duplication is ruled
out by exact stream-cut labels and occurrence uniqueness of the supplied mixed inventory.
This is one licensing clause, not a proof that the object cuts themselves are licensed.
-/
theorem StreamFailureCuts.rootStream_not_cancelled_mixed
    {work events streamCuts objectCuts failures before cut occurrence after stream errors
      matching}
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (unique : (failures.map Prod.snd).Nodup)
    (generated : ExecutedWork work)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (root : NodeAt work stream .stream [] none)
    (member : (cut, occurrence) ∈ streamCuts)
    (atEvent : events[cut]? = some (.streamFailure stream errors))
    (split : failures = before ++ (cut, occurrence) :: after)
    : ¬TaskCancelled work matching (events.take cut) before occurrence := by
  obtain ⟨node, count, producer, selected, task⟩ := cuts.2 _ member
  obtain ⟨sameNode, sameCount⟩ :=
    Execution.WorkQueueEvent.streamFailure.inj (Option.some.inj (selected.symm.trans atEvent))
  subst node count
  obtain ⟨dependencies, located⟩ := (itemTask_owner_nodeAt task).2
  have sameProducer := generated.streamProducer_unique located root rfl
  subst producer
  intro cancelled
  obtain ⟨earlier, owners, ⟨producer, payload, known⟩, owner, failed⟩ :=
    (generated.rootStream_nodeFailed_iff root).mp (cancelled.singleton_root_failed task)
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp failed
  obtain ⟨inBefore, reached⟩ := List.mem_filter.mp kept
  have within : entry.1 ≤ cut := by
    have bound : entry.1 ≤ (events.take cut).length := by simpa using reached
    exact Nat.le_trans bound (List.length_take_le _ _)
  have inAll : entry ∈ failures := by rw [split]; exact List.mem_append_left _ inBefore
  rcases List.mem_append.mp (partition.mem_iff.mp inAll) with fromStream | fromObject
  · obtain ⟨priorNode, count, birth, atPrior, priorTask⟩ := cuts.2 entry fromStream
    rw [same] at priorTask
    rw [← (priorTask.unique known).1] at owner
    have sameRef := List.mem_singleton.mp owner
    have less : entry.1 < cut := by
      by_cases earlier : entry.1 < cut
      · exact earlier
      apply False.elim
      have equal : entry.1 = cut := by omega
      have sameEntry := cuts.unique_at fromStream member equal
      have duplicate : entry.2 ∈ before.map Prod.snd :=
        List.mem_map.mpr ⟨entry, inBefore, rfl⟩
      rw [sameEntry] at duplicate
      rw [split, List.map_append, List.map_cons] at unique
      exact (List.nodup_append.mp unique).2.2 occurrence duplicate occurrence
        List.mem_cons_self rfl
    exact streamFailure_refs_ne ordered atPrior atEvent less sameRef.symm
  · obtain ⟨otherOwners, birth, path, count, object⟩ := objects entry fromObject
    rw [same] at object
    exact generated.objectFailure_not_streamOwner root object ((known.unique object).1 ▸ owner)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
