import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferences
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeProjection

/-! Announcement evidence for live roots and pending internal group failures. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open WorkQueueSemantics

/-- Output justifies the result's active groups and every failed closure's prior notice.
The initial refs describe already announced groups; openness and freshness are separate.
-/
def GroupFailureNoticeAccounting (initial : NodeRefs)
    (result : State × List WorkQueueEvent)
    : Prop :=
  result.1.rootGroups.Subset (initial ++ result.2.flatMap rawGroupNoticeRefs)
  ∧ ReferencesAnnounced rawGroupNoticeRefs rawGroupFailureRefs initial result.2

/-- Enlarging the initial notice set preserves both accounting clauses.
Witness: subset transport for roots and monotonicity of strict-prefix references.
-/
theorem GroupFailureNoticeAccounting.mono {initial more result}
    (accounted : GroupFailureNoticeAccounting initial result)
    (included : initial.Subset more)
    : GroupFailureNoticeAccounting more result := by
  refine ⟨?_, accounted.2.mono included⟩
  intro ref member
  exact (List.mem_append.mp (accounted.1 member)).elim
    (fun old => List.mem_append_left _ (included old))
    (fun added => List.mem_append_right _ added)

/-- Sequential output segments preserve the notice-before-failure boundary.
Witness: the first segment supplies all roots used by the next segment, and actual
notice lists concatenate in output order. No lifecycle premise is used.
-/
theorem GroupFailureNoticeAccounting.append {initial first second}
    (before : GroupFailureNoticeAccounting initial first)
    (after : GroupFailureNoticeAccounting first.1.rootGroups second)
    : GroupFailureNoticeAccounting initial (second.1, first.2 ++ second.2) := by
  have later := after.mono before.1
  refine ⟨?_, before.2.append later.2⟩
  simpa only [List.flatMap_append, List.append_assoc] using later.1

/-- Immediate output accounts for active roots; queued startup failures may use every
notice in that immediate output. Dispatch enqueues them for their later FIFO positions.
-/
def StartupFailureNoticeAccounting (initial : NodeRefs)
    (result : State × List WorkQueueEvent × List GroupFailureEvent)
    : Prop :=
  GroupFailureNoticeAccounting initial (result.1, result.2.1)
  ∧ ∀ failure ∈ result.2.2,
      failure.group.ref ∈ initial ++ result.2.1.flatMap rawGroupNoticeRefs

/-- Consecutive transitions retain prior notices for both immediate and queued failures. -/
theorem StartupFailureNoticeAccounting.append {initial first second}
    (before : StartupFailureNoticeAccounting initial first)
    (after : StartupFailureNoticeAccounting first.1.rootGroups second)
    : StartupFailureNoticeAccounting initial
        (second.1, first.2.1 ++ second.2.1, first.2.2 ++ second.2.2) := by
  refine ⟨before.1.append after.1, ?_⟩
  intro failure member
  simp only [List.flatMap_append]
  rcases List.mem_append.mp member with earlier | later
  · rcases List.mem_append.mp (before.2 failure earlier) with old | noticed
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (List.mem_append_left _ noticed)
  · rcases List.mem_append.mp (after.2 failure later) with root | noticed
    · rcases List.mem_append.mp (before.1.1 root) with old | previous
      · exact List.mem_append_left _ old
      · exact List.mem_append_right _ (List.mem_append_left _ previous)
    · exact List.mem_append_right _ (List.mem_append_right _ noticed)

/-- Enlarging the initial announcement inventory preserves local startup effects. -/
theorem StartupFailureNoticeAccounting.mono {initial more result}
    (accounted : StartupFailureNoticeAccounting initial result)
    (included : initial.Subset more)
    : StartupFailureNoticeAccounting more result := by
  refine ⟨accounted.1.mono included, ?_⟩
  intro failure member
  rcases List.mem_append.mp (accounted.2 failure member) with old | noticed
  · exact List.mem_append_left _ (included old)
  · exact List.mem_append_right _ noticed

/-- Refs whose announcements must remain available while their internal notices wait. -/
def State.pendingGroupFailureRefs (queue : State) : NodeRefs :=
  queue.groupFailureEvents.map (fun failure => failure.group.ref)

/-- Live roots and queued notices both retain earlier announcement evidence. -/
def State.groupNoticeSupport (queue : State) : NodeRefs :=
  queue.rootGroups ++ queue.pendingGroupFailureRefs

/-- Output preserves announcements for active roots and pending failure controls.
The pending clause retains history after startup has removed a failed group's live shell.
This is proof evidence, separate from runtime notice payloads and source admission. -/
def FifoFailureNoticeAccounting (initial : NodeRefs)
    (result : State × List WorkQueueEvent)
    : Prop :=
  GroupFailureNoticeAccounting initial result
  ∧ result.1.pendingGroupFailureRefs.Subset
      (initial ++ result.2.flatMap rawGroupNoticeRefs)

/-- An empty FIFO segment retains its input announcement inventory. -/
theorem FifoFailureNoticeAccounting.refl (queue : State)
    : FifoFailureNoticeAccounting queue.groupNoticeSupport (queue, []) := by
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · intro ref member
    simp only [List.flatMap_nil, List.append_nil]
    exact List.mem_append_left _ member
  · intro ref member
    simp only [List.flatMap_nil, List.append_nil]
    exact List.mem_append_right _ member

/-- Both components of the next FIFO step's announcement inventory are supported. -/
theorem FifoFailureNoticeAccounting.known {initial result}
    (accounted : FifoFailureNoticeAccounting initial result)
    : result.1.groupNoticeSupport.Subset
        (initial ++ result.2.flatMap rawGroupNoticeRefs) := by
  intro ref member
  exact (List.mem_append.mp member).elim (fun present => accounted.1.1 present)
    (fun pending => accounted.2 pending)

/-- A larger initial inventory preserves pending and emitted announcement evidence. -/
theorem FifoFailureNoticeAccounting.mono {initial more result}
    (accounted : FifoFailureNoticeAccounting initial result)
    (included : initial.Subset more)
    : FifoFailureNoticeAccounting more result := by
  refine ⟨accounted.1.mono included, ?_⟩
  intro ref member
  rcases List.mem_append.mp (accounted.2 member) with old | noticed
  · exact List.mem_append_left _ (included old)
  · exact List.mem_append_right _ noticed

/-- Actual FIFO segments compose while retaining queued controls' prior announcements. -/
theorem FifoFailureNoticeAccounting.append {initial first second}
    (before : FifoFailureNoticeAccounting initial first)
    (after : FifoFailureNoticeAccounting first.1.groupNoticeSupport second)
    : FifoFailureNoticeAccounting initial (second.1, first.2 ++ second.2) := by
  have later := after.mono before.known
  refine ⟨⟨?_, before.1.2.append later.1.2⟩, ?_⟩
  · simpa only [List.flatMap_append, List.append_assoc] using later.1.1
  · simpa only [List.flatMap_append, List.append_assoc] using later.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
