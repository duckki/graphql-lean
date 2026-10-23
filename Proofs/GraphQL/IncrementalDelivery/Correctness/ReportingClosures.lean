import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingAccounting

/-! Close an accounted reporting frontier without losing retained failed notices.
ID closure is kept separate from the actual scope obligation for termination.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Failure-only closure preserves the reporting frontier
-----------------------------------------------------------------------------------------

/-- A failed open ref has a notice-free closure preserving reporting-aware coverage.
Witness: its existing failure count supplies a permitted completion; no producer publishes,
and closing an already-failed ref satisfies no healthy defer dependency. Its selected positive cause supplies the count; inherited failure alone does not
license an error completion.
-/
theorem reporting_complete_failed
    {ancestry bound roles work groups streams events matching failures node kind
      dependencies producer}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (known : NodeAt work node kind dependencies producer)
    (opened : Open ((groups ++ streams).map DeliveryNode.ref) events node.ref)
    (failed : NodeFailed work matching events failures node.ref)
    (accounted : NodeAccounted work matching events failures node.ref)
    (cause
      : ∃ errors,
          NodeFailureCause work (failedBefore failures events.length) node.ref errors)
    : ∃ event,
        Explains work groups streams (events ++ [event]) matching failures
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            matching (events ++ [event]) failures
        ∧ eventPending event = []
        ∧ eventCompleted event = [node.ref]
        ∧ ¬IsValue event := by
  obtain ⟨event, allowed, pending, completed, control⟩ := completion_exists known opened
    accounted (fun _ => cause)
  have extended := explained.append_event allowed
  have failureTransport : ∀ ref, NodeFailed work matching events failures ref →
      NodeFailed work matching (events ++ [event]) failures ref :=
    fun _ failure => failure.append _
  have notices : (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events).Subset
      (announcedRefs ((groups ++ streams).map DeliveryNode.ref) (events ++ [event])) := by
    intro ref member
    simpa [announcedRefs, pendingRefs, pending] using member
  have completions : ∀ ref, roles ref = false →
      ¬NodeFailed work matching (events ++ [event]) failures ref →
      ref ∈ completedRefs (events ++ [event]) → ref ∈ completedRefs events := by
    intro ref _ healthy closed
    simp only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, completed, List.mem_append, List.mem_singleton] at closed
    rcases closed with earlier | rfl
    · exact earlier
    · exact False.elim (healthy (failed.append [event]))
  have publications : ∀ task, Published matching (events ++ [event]) task →
      Published matching events task := by
    intro task published
    rcases published_append_singleton_iff.mp published with earlier | ⟨value, _⟩
    · exact earlier
    · exact False.elim (control value)
  have retained := supported_coverage_control valid coherent roleCoherent explained covered.1
    extended failureTransport notices completions publications (fun _ accounted =>
      accounted.append [event])
  refine ⟨event, extended, ?_, pending, completed, control⟩
  apply group_notices_covered_noncarrier valid coherent roleCoherent covered retained
    extended failureTransport notices completions
    (fun _ _ _ _ task published =>
      explained.published_producer task (publications _ published))
    (fun _ _ _ _ notice source generated =>
      publications _ (notice.2.2.1 source generated))
  intro ref recorded
  obtain ⟨task, owners, settled, descriptor, member⟩ := recorded
  refine ⟨task, owners, ?_, descriptor, member⟩
  rw [explained.2.1.failedBefore_eq (Nat.le_refl events.length)]
  rwa [explained.2.1.failedBefore_eq (by simp)] at settled

-----------------------------------------------------------------------------------------
-- All remaining open refs can close without an extra carrier
-----------------------------------------------------------------------------------------

/-- Close a finite failed frontier while retaining constructive notice coverage.
Witness: one permitted failure completion per remaining open ref; notices and publications
stay unchanged, accounting persists, and healthy refs that already closed stay closed.
This constructs closures, not a terminal history or a proof of response-path coverage.
-/
theorem close_reporting_frontier
    {ancestry bound roles work groups streams events matching failures}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (causes
      : OpenFailureCauses work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (covered
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → TaskAccounted work matching events failures occurrence)
    (healthyClosed
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ¬NodeFailed work matching events failures ref → ref ∈ completedRefs events)
    (remaining : NodeRefs)
    (covers
      : ∀ ref,
          Open ((groups ++ streams).map DeliveryNode.ref) events ref → ref ∈ remaining)
    : ∃ tail,
        tail.length ≤ remaining.length
        ∧ (∀ event ∈ tail, eventPending event = [] ∧ ¬IsValue event)
        ∧ Explains work groups streams (events ++ tail) matching failures
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            matching (events ++ tail) failures
        ∧ ∀ ref ∈
            announcedRefs ((groups ++ streams).map DeliveryNode.ref) (events ++ tail),
            ref ∈ completedRefs (events ++ tail) := by
  classical
  induction remaining generalizing events with
  | nil =>
      refine ⟨[], by simp, by simp, by simpa using explained, by simpa using covered, ?_⟩
      intro ref announced
      by_cases closed : ref ∈ completedRefs (events ++ [])
      · exact closed
      · have opened : Open ((groups ++ streams).map DeliveryNode.ref) events ref := by
          simpa only [Open, List.append_nil] using And.intro announced closed
        exact False.elim (List.not_mem_nil (covers ref opened))
  | cons ref rest ih =>
      by_cases opened : Open ((groups ++ streams).map DeliveryNode.ref) events ref
      · obtain ⟨node, kind, dependencies, producer, known, same⟩ :=
          explained.noticeFacts.supported ref opened.1
        have failed : NodeFailed work matching events failures ref := by
          apply Classical.byContradiction
          intro healthy
          exact opened.2 (healthyClosed ref opened.1 healthy)
        have nodeAccounted : NodeAccounted work matching events failures node.ref := by
          rintro task owners ⟨birth, payload, descriptor⟩ _
          exact accounted task owners birth payload descriptor
        obtain ⟨event, extended, retained, pending, completed, control⟩ :=
          reporting_complete_failed valid coherent roleCoherent explained covered known
            (same ▸ opened) (same ▸ failed) nodeAccounted
            (same ▸ causes ref opened failed)
        have nextHealthy : ∀ other ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref)
            (events ++ [event]), ¬NodeFailed work matching (events ++ [event]) failures other →
            other ∈ completedRefs (events ++ [event]) := by
          intro other announced healthy
          have prior : other ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref)
              events := by simpa [announcedRefs, pendingRefs, pending] using announced
          have closed := healthyClosed other prior (fun failed => healthy (failed.append _))
          simpa only [completedRefs, List.flatMap_append]
            using List.mem_append_left (completedRefs [event]) closed
        obtain ⟨tail, bounded, controls, finished, frontier, closed⟩ := ih extended
          (causes.append_completion explained.2.1 pending completed) retained
          (fun task owners birth payload known =>
            (accounted task owners birth payload known).append [event]) nextHealthy (by
            intro other active
            have facts := (open_append_completion pending completed).mp active
            rcases List.mem_cons.mp (covers other facts.1) with equal | member
            · exact False.elim (facts.2 (equal.trans same.symm))
            · exact member)
        refine ⟨event :: tail, by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_⟩
        · intro next member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨pending, control⟩
          · exact controls next member
        · simpa only [List.append_assoc, List.singleton_append] using finished
        · simpa only [List.append_assoc, List.singleton_append] using frontier
        · simpa only [List.append_assoc, List.singleton_append] using closed
      · obtain ⟨tail, bounded, controls, finished, frontier, closed⟩ := ih explained causes covered
          accounted healthyClosed (by
            intro other active
            rcases List.mem_cons.mp (covers other active) with equal | member
            · exact False.elim (opened (equal ▸ active))
            · exact member)
        exact ⟨tail, Nat.le_trans bounded (by simp), controls, finished, frontier, closed⟩

-----------------------------------------------------------------------------------------
-- Accounted mixed work can close its IDs while retaining reporting opportunities
-----------------------------------------------------------------------------------------

/-- A reporting-covered mixed prefix extends to accounted work and closed announced IDs.
Witness: the reporting-aware maximal extension closes every healthy announced ref, then
bounded failure-only closure preserves its frontier and dependency satisfaction. This
does not discharge the missing-attachment scope obligation or assert Terminal.
-/
theorem mixed_reporting_closed_extension
    {ancestry bound roles paths pathBound work groups streams head matching failures}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (allocated : (streamAllocationRefs work).Nodup)
    (positive : ExecutionErrors.WorkPositive work)
    (initial : Explains work groups streams head matching failures)
    (coverage
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching head failures)
    (support
      : StreamNoticesSupported ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching head failures)
    : ∃ tail next cuts,
        Explains work groups streams (head ++ tail) next cuts
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            next (head ++ tail) cuts
        ∧ (∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload
            → TaskAccounted work next (head ++ tail) cuts occurrence)
        ∧ (∀ ref ∈
            announcedRefs ((groups ++ streams).map DeliveryNode.ref) (head ++ tail),
            ref ∈ completedRefs (head ++ tail))
        ∧ ∀ ref,
            ¬NodeFailed work next (head ++ tail) cuts ref
            → DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) next
                (head ++ tail) cuts ref := by
  obtain ⟨tail, next, cuts, explained, covered, causes, accounted, dependencies⟩ :=
    mixed_reporting_accounted_extension valid coherent roleCoherent continuous ordered
      pathCoherent allocated positive initial coverage support
  have healthyClosed : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref)
      (head ++ tail), ¬NodeFailed work next (head ++ tail) cuts ref →
      ref ∈ completedRefs (head ++ tail) := by
    intro ref announced healthy
    obtain ⟨node, kind, parents, producer, known, same⟩ :=
      explained.noticeFacts.supported ref announced
    rcases (dependencies ref healthy).2 with absent | closed | ⟨fresh, _⟩
    · exact False.elim (absent ⟨producer, node, kind, parents, known, same⟩)
    · exact closed
    · exact False.elim (fresh announced)
  obtain ⟨closures, _, controls, finished, frontier, closed⟩ := close_reporting_frontier
    valid coherent roleCoherent explained causes covered accounted healthyClosed
    (announcedRefs ((groups ++ streams).map DeliveryNode.ref) (head ++ tail))
    (fun _ opened => opened.1)
  have satisfied : ∀ ref, ¬NodeFailed work next (head ++ tail ++ closures) cuts ref →
      DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) next
        (head ++ tail ++ closures) cuts ref := by
    intro ref healthy
    refine ⟨healthy, ?_⟩
    rcases (dependencies ref (fun failed => healthy (failed.append closures))).2
      with absent | completed | ⟨fresh, accounted⟩
    · exact Or.inl absent
    · exact Or.inr (Or.inl (by
        simpa only [completedRefs, List.flatMap_append]
          using List.mem_append_left (completedRefs closures) completed))
    · refine Or.inr (Or.inr ⟨?_, accounted.append closures⟩)
      have pending : closures.flatMap eventPending = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro event member
        exact (controls event member).1
      simpa only [announcedRefs, pendingRefs, List.flatMap_append, pending,
        List.append_nil]
        using fresh
  refine ⟨tail ++ closures, next, cuts, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using finished
  · simpa only [List.append_assoc] using frontier
  · intro occurrence owners producer payload known
    simpa only [List.append_assoc] using (accounted occurrence owners producer payload known).append
      closures
  · simpa only [List.append_assoc] using closed
  · simpa only [List.append_assoc] using satisfied

end GraphQL.IncrementalDelivery.Correctness
