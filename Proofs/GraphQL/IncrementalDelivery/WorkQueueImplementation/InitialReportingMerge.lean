import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReportingAvailability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.HistoryExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.ReportingWitness

/-! Merge initial reporting availability with later observations without repeated occurrences. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem reporting_tail {work initial events head rest}
    (witness : FailureReportingWitness work initial events (head :: rest))
    : FailureReportingWitness work initial events rest := by
  intro before cut occurrence after split
  have full := witness (head :: before) cut occurrence after (by simp [split])
  exact ⟨full.1, fun earlier member => full.2.1 earlier (List.mem_cons_of_mem _ member),
    fun prior => full.2.2.1 (List.mem_cons_of_mem _ prior), full.2.2.2⟩

/-- Reporting witnesses retain nondecreasing cuts and distinct occurrences. -/
theorem reporting_metadata {work initial events reported}
    (witness : FailureReportingWitness work initial events reported)
    : reported.Pairwise (fun left right => left.1 ≤ right.1)
      ∧ (reported.map Prod.snd).Nodup := by
  induction reported with
  | nil => simp
  | cons head rest ih =>
      have tail := ih (reporting_tail witness)
      refine ⟨List.pairwise_cons.mpr ⟨?_, tail.1⟩, ?_⟩
      · intro later member
        obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
        exact (witness (head :: before) later.1 later.2 after (by simp [split])).2.1
          head List.mem_cons_self
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, tail.2⟩
        intro member
        obtain ⟨later, included, same⟩ := List.mem_map.mp member
        obtain ⟨before, after, split⟩ := List.mem_iff_append.mp included
        have fresh := (witness (head :: before) later.1 later.2 after (by simp [split])).2.2.1
        exact fresh (List.mem_cons.mpr (.inl same))

/-- Each available entry retains its exact reachable failed descriptor and announcement. -/
theorem reporting_entry {work initial events reported entry}
    (witness : FailureReportingWitness work initial events reported)
    (member : entry ∈ reported)
    : entry.1 ≤ events.length
      ∧ ∃ owners producer payload,
          TaskAt work entry.2 owners producer payload
          ∧ payload.failure.isSome = true
          ∧ Reachable work entry.2
          ∧ ∃ ref ∈ owners, ref ∈ announcedRefs initial (events.take entry.1) := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have facts := witness before entry.1 entry.2 after split
  exact ⟨facts.1, facts.2.2.2⟩

/-- Retain initial availability and discard later duplicate reporting entries.
This combines existential observation evidence, without changing either runtime replay.
-/
noncomputable def prependInitialReporting (first later : FailureCuts) : FailureCuts := by
  classical
  exact first ++ later.filter (fun entry => decide (entry.2 ∉ first.map Prod.snd))

/-- Initial reporting cuts at zero compose with a later licensed reporting witness. -/
theorem prependInitialReporting_witness {work initial events first later}
    (initialWitness : FailureReportingWitness work initial events first)
    (laterWitness : FailureReportingWitness work initial events later)
    (zero : ∀ entry ∈ first, entry.1 = 0)
    : FailureReportingWitness work initial events
        (prependInitialReporting first later) := by
  classical
  have early := reporting_metadata initialWitness
  have late := reporting_metadata laterWitness
  have ordered : (prependInitialReporting first later).Pairwise
      (fun left right => left.1 ≤ right.1) := by
    apply List.pairwise_append.mpr
    refine ⟨early.1, late.1.filter _, ?_⟩
    intro left member right _
    rw [zero left member]
    exact Nat.zero_le _
  have distinct : ((prependInitialReporting first later).map Prod.snd).Nodup := by
    rw [prependInitialReporting, List.map_append]
    apply List.nodup_append.mpr
    refine ⟨early.2, late.2.sublist (List.filter_sublist.map _), ?_⟩
    intro occurrence prior other member same
    obtain ⟨entry, included, identity⟩ := List.mem_map.mp member
    have absent : entry.2 ∉ first.map Prod.snd := by
      exact of_decide_eq_true (List.mem_filter.mp included).2
    exact absent (by rwa [identity, ← same])
  intro before cut occurrence after split
  have member : (cut, occurrence) ∈ prependInitialReporting first later := by simp [split]
  have known := (List.mem_append.mp member).elim
    (fun early => reporting_entry initialWitness early)
    (fun late => reporting_entry laterWitness (List.mem_filter.mp late).1)
  refine ⟨known.1, ?_, ?_, known.2⟩
  · rw [split] at ordered
    intro earlier included
    exact (List.pairwise_append.mp ordered).2.2 earlier included _ List.mem_cons_self
  · rw [split, List.map_append, List.map_cons] at distinct
    intro prior
    exact (List.nodup_append.mp distinct).2.2 _ prior _ List.mem_cons_self rfl

/-- Every later observation remains available at its original cut or an earlier initial cut. -/
theorem prependInitialReporting_available (first later : FailureCuts)
    (zero : ∀ entry ∈ first, entry.1 = 0)
    : CausalFailuresAvailable later (prependInitialReporting first later) := by
  classical
  intro cut occurrence member
  by_cases earlier : occurrence ∈ first.map Prod.snd
  · obtain ⟨entry, included, same⟩ := List.mem_map.mp earlier
    refine ⟨0, List.mem_append_left _ ?_, Nat.zero_le _⟩
    have identity : entry = (0, occurrence) := Prod.ext (zero entry included) same
    exact identity ▸ included
  · refine ⟨cut, List.mem_append_right _ (List.mem_filter.mpr ⟨member, ?_⟩), Nat.le_refl _⟩
    exact decide_eq_true earlier

/-- Retaining initial entries preserves every initial cause at each output boundary. -/
theorem prependInitialReporting_initial (first later : FailureCuts) (cut : Nat)
    : (failedBefore first cut).Subset
        (failedBefore (prependInitialReporting first later) cut) := by
  intro occurrence member
  simp only [failedBefore, List.mem_map, List.mem_filter, decide_eq_true_eq] at member ⊢
  obtain ⟨entry, ⟨included, bounded⟩, same⟩ := member
  exact ⟨entry, ⟨List.mem_append_left _ included, bounded⟩, same⟩

/-- Later available causes remain available after replacing repeated entries by earlier cuts. -/
theorem prependInitialReporting_later (first later : FailureCuts)
    (zero : ∀ entry ∈ first, entry.1 = 0) (cut : Nat)
    : (failedBefore later cut).Subset
        (failedBefore (prependInitialReporting first later) cut) := by
  exact (prependInitialReporting_available first later zero).failedBefore_subset cut

/-- A joint available cause comes from an initial observation or a bounded source cut. -/
theorem prependInitialReporting_failedBefore_subset (first later : FailureCuts)
    (cut : Nat)
    : (failedBefore (prependInitialReporting first later) cut).Subset
        (first.map Prod.snd ++ failedBefore later cut) := by
  classical
  intro occurrence member
  obtain ⟨entry, selected, same⟩ := List.mem_map.mp member
  obtain ⟨included, bounded⟩ := List.mem_filter.mp selected
  rcases List.mem_append.mp included with initial | source
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨entry, initial, same⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr
      ⟨entry, List.mem_filter.mpr ⟨(List.mem_filter.mp source).1, bounded⟩, same⟩)

/-- Existing causal availability survives deduplication against earlier initial reporting. -/
theorem prependInitialReporting_causal {failures first later : FailureCuts}
    (available : CausalFailuresAvailable failures later)
    (zero : ∀ entry ∈ first, entry.1 = 0)
    : CausalFailuresAvailable failures (prependInitialReporting first later) := by
  intro cut occurrence member
  obtain ⟨laterCut, reported, before⟩ := available cut occurrence member
  obtain ⟨earlyCut, retained, earlier⟩ :=
    prependInitialReporting_available first later zero laterCut occurrence reported
  exact ⟨earlyCut, retained, Nat.le_trans earlier before⟩

/-- Initial aggregate causes and later reporting share one fresh licensed inventory.
Later causal failures can use the earlier initial entries without duplicate reporting cuts.
-/
theorem ExecutedWork.initialStartup_mergeReporting {work startup}
    (generated : ExecutedWork work) (matched : InitialStartup.MatchesWork startup work)
    (events : List Execution.WorkQueueEvent) (later : FailureCuts)
    (laterWitness
      : let initial := State.initialize (Work.fromExecution work) startup
        FailureReportingWitness work
          ((initial.initialGroups ++ initial.initialStreams).map
            Execution.DeliveryNode.ref)
          events later)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      ∃ reported,
        FailureReportingWitness work refs events reported
        ∧ CausalFailuresAvailable later reported
        ∧ (∀ cut, (failedBefore later cut).Subset (failedBefore reported cut))
        ∧ ∀ failure ∈ initial.groupFailureEvents,
            ∀ cut,
              NodeFailureCauses work (failedBefore reported cut) failure.group.ref
                failure.errors := by
  dsimp only at laterWitness ⊢
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  let early := startup.reportingCuts work refs
  have zero : ∀ entry ∈ early, entry.1 = 0 := by
    intro entry member
    obtain ⟨occurrence, _, same⟩ := List.mem_map.mp member
    exact (congrArg Prod.fst same).symm
  refine ⟨
    prependInitialReporting early later,
    prependInitialReporting_witness (InitialStartup.reportingWitness matched events)
      laterWitness zero,
    prependInitialReporting_available early later zero,
    prependInitialReporting_later early later zero,
    ?_
  ⟩
  intro failure emitted cut
  have supported := generated.initialStartup_reportingCauses startup matched failure emitted
  have same := startup.failedBefore_reportingCuts work refs cut
  rw [startup.failedBefore_reportingCuts work refs 0, ← same] at supported
  exact supported.mono (prependInitialReporting_initial early later cut)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
