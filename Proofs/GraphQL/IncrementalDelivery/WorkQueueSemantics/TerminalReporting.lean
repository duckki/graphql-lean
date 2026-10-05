import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.EventLifecycle

/-! Terminal cancellation reporting, independent of response reconstruction. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Reports persist and cover descendant attachment paths
-----------------------------------------------------------------------------------------

/-- A failure report remains available after further work events.
Witness: the same positive-error completion remains a member of the appended history.
-/
theorem FailureReportedFor.append {events path}
    (reported : FailureReportedFor events path) (tail : List WorkQueueEvent)
    : FailureReportedFor (events ++ tail) path := by
  obtain ⟨node, errors, positive, below, failure⟩ := reported
  exact ⟨node, errors, positive, below,
    failure.imp (List.mem_append_left tail) (List.mem_append_left tail)⟩

/-- A reported scope also covers every descendant of the supplied attachment path.
Witness: transitivity of response-path prefixes, retaining the same completion event.
-/
theorem FailureReportedFor.descendant {events path descendant}
    (reported : FailureReportedFor events path) (below : path.IsPrefix descendant)
    : FailureReportedFor events descendant := by
  obtain ⟨node, errors, positive, scope, failure⟩ := reported
  exact ⟨node, errors, positive, scope.trans below, failure⟩

-----------------------------------------------------------------------------------------
-- Work batching cannot lose a report
-----------------------------------------------------------------------------------------

/-- Only value events can participate in adjacent value coalescing.
Witness: inspection of the two permitted combineValues branches.
-/
private theorem combineValues_isValue {left right merged}
    (combined : combineValues left right = some merged)
    : IsValue left ∧ IsValue right ∧ IsValue merged := by
  cases left <;> cases right <;> simp [combineValues] at combined
  all_goals obtain ⟨_, rfl⟩ := combined; exact ⟨trivial, trivial, trivial⟩

/-- Optional value coalescing preserves each nonvalue event exactly.
Witness: grouping induction; neither input nor output of a merge can equal a control.
-/
theorem ValueGrouping.control_mem {events grouped event}
    (grouping : ValueGrouping events grouped) (control : ¬IsValue event)
    : event ∈ grouped ↔ event ∈ events := by
  induction grouping with
  | nil => simp
  | separate head _ ih => simpa only [List.mem_cons] using or_congr Iff.rfl ih
  | @combine head tail first rest merged grouping compatible ih =>
      obtain ⟨left, right, merged⟩ := combineValues_isValue compatible
      have differentLeft : event ≠ head := fun equal => control (equal ▸ left)
      have differentRight : event ≠ first := fun equal => control (equal ▸ right)
      have differentMerged : event ≠ _ := fun equal => control (equal ▸ merged)
      simpa only [List.mem_cons, differentLeft, differentRight, differentMerged,
        false_or] using ih

/-- Work-event batching preserves nonvalue-event membership across all batches.
Witness: partition induction and exact control preservation under value grouping.
-/
theorem WorkBatching.control_mem {events batches event}
    (batching : WorkBatching events batches) (control : ¬IsValue event)
    : event ∈ batches.flatten ↔ event ∈ events := by
  induction batching with
  | nil => simp
  | cons _ grouping _ ih =>
      simp only [List.flatten_cons, List.mem_append, grouping.control_mem control, ih]

/-- A positive-error report survives every permitted work-event batching choice.
Witness: control membership preserves its exact node descriptor and error count.
-/
theorem WorkBatching.failure_reported {events batches path}
    (batching : WorkBatching events batches) (reported : FailureReportedFor events path)
    : FailureReportedFor batches.flatten path := by
  obtain ⟨node, errors, positive, below, failure⟩ := reported
  refine ⟨node, errors, positive, below, ?_⟩
  rcases failure with member | member
  · exact Or.inl ((batching.control_mem (by simp [IsValue])).mpr member)
  · exact Or.inr ((batching.control_mem (by simp [IsValue])).mpr member)

-----------------------------------------------------------------------------------------
-- Read-side consequences of terminal reporting
-----------------------------------------------------------------------------------------

/-- Terminal reporting retains the earlier internal task-accounting consequence.
Witness: discard the report from a cancelled task, or retain its publication evidence.
-/
theorem Terminal.tasks_accounted {work initial matching events failures}
    (terminal : Terminal work initial matching events failures)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : TaskAccounted work matching events failures occurrence := by
  rcases terminal.1 occurrence owners producer payload known with cancelled | published
  · exact Or.inl cancelled.1
  · exact Or.inr published

/-- Every unpublished terminal task has a client-decodable work-level failure scope.
Witness: publication exclusion selects the cancellation-and-report branch of Terminal.
-/
theorem Terminal.failure_reported {work initial matching events failures}
    (terminal : Terminal work initial matching events failures)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (unpublished : ¬Published matching events occurrence)
    : FailureReportedFor events payload.path :=
  ((terminal.1 occurrence owners producer payload known).resolve_right unpublished).2

/-- A reported scope belongs to a known, announced node in any explained history.
Witness: locate the completion event and project its admission premises at that prefix.
The report does not require its ID still to be open at the end of the history.
-/
theorem Explains.failure_report_known {work groups streams events matching failures path}
    (explained : Explains work groups streams events matching failures)
    (reported : FailureReportedFor events path)
    : ∃ node kind dependencies producer,
        NodeAt work node kind dependencies producer
        ∧ node.path.IsPrefix path
        ∧ node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events := by
  obtain ⟨node, errors, _, below, failure⟩ := reported
  rcases failure with member | member
  all_goals
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    have allowed := explained.2.2 index _ selected
    obtain ⟨dependencies, producer, known⟩ := allowed.1
    refine ⟨node, _, dependencies, producer, known, below, ?_⟩
    apply explained.noticeFacts.closed node.ref
    apply List.mem_flatMap.mpr
    exact ⟨_, member, by simp [eventCompleted]⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
