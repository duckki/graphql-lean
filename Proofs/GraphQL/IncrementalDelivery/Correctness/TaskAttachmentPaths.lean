import Proofs.GraphQL.IncrementalDelivery.Correctness.ExecutionPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TerminalReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting

/-! Failure scopes propagate down generated producer attachments, not just node refs. -/

namespace GraphQL.IncrementalDelivery.Correctness.ExecutionPaths
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Structural lookup retains the nearest producer's attachment bound
-----------------------------------------------------------------------------------------

/-- A selected stream entry inherits its list's child-work certificate.
Witness: membership induction through the certificate's item-list clauses.
-/
theorem ItemsUnder.member {base items} (under : ItemsUnder base items)
    {result children} (member : (result, children) ∈ items)
    : WorkUnder base children := by
  induction items with
  | nil => cases member
  | cons entry rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst entry; exact under.1
      · exact ih under.2 later

/-- A located subtree has a local bound below `base` and below its nearest producer's
attachment. Witness: navigation induction; combine preserves the bound, while execution
groups and stream items install their own producer-local bound.
-/
theorem WorkUnder.located {base work address current producer enclosing}
    (under : WorkUnder base work)
    (located : Located work address current producer enclosing)
    : ∃ localPath,
        WorkUnder localPath current
        ∧ base.IsPrefix localPath
        ∧ ∀ occurrence,
            producer = some occurrence
            → ∃ owners ancestor payload,
                TaskAt work occurrence owners ancestor payload
                ∧ payload.path.IsPrefix localPath := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact ⟨base, under, ⟨[], by simp⟩, by simp⟩
  | left _ ih =>
      obtain ⟨path, certified, below, parent⟩ := ih
      exact ⟨path, certified.1, below, parent⟩
  | right _ ih =>
      obtain ⟨path, certified, below, parent⟩ := ih
      exact ⟨path, certified.2, below, parent⟩
  | @executionGroup address groups path result children birth enclosing located ih =>
      obtain ⟨localPath, certified, below, _⟩ := ih
      refine ⟨path, certified.2, below.trans certified.1, ?_⟩
      intro occurrence same
      cases same
      exact ⟨_, _, _, .executionGroup located.toCurrent, ⟨[], by simp [Payload.path]⟩⟩
  | @item address node items birth enclosing index result children located entry ih =>
      obtain ⟨localPath, certified, below, _⟩ := ih
      refine ⟨node.path, certified.2.member (List.mem_of_getElem? entry),
        below.trans certified.1, ?_⟩
      intro occurrence same
      cases same
      exact ⟨_, _, _, .item located.toCurrent entry, ⟨[], by simp [Payload.path]⟩⟩

/-- Every task attachment lies below the work's outer bound.
Witness: its local navigation bound and the execution-group or stream attachment clause.
-/
theorem WorkUnder.task_under {base work occurrence owners producer payload}
    (under : WorkUnder base work)
    (known : TaskAt work occurrence owners producer payload)
    : base.IsPrefix payload.path := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨_, certified, below, _⟩ := under.located located.toCurrent
      exact below.trans certified.1
  | item located _ =>
      obtain ⟨_, certified, below, _⟩ := under.located located.toCurrent
      exact below.trans certified.1

/-- Every task attachment stays below its structural producer's attachment.
Witness: the nearest-producer bound from navigation and functional task uniqueness.
This is a response-path fact, not an imposed ordering of work-event settlements.
-/
theorem WorkUnder.producer_prefix
    {base work occurrence owners producer payload parentOwners ancestor parentPayload}
    (under : WorkUnder base work)
    (known : TaskAt work occurrence owners (some producer) payload)
    (parent : TaskAt work producer parentOwners ancestor parentPayload)
    : parentPayload.path.IsPrefix payload.path := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨path, certified, _, parentKnown⟩ := under.located located.toCurrent
      obtain ⟨_, _, _, descriptor, below⟩ := parentKnown producer rfl
      have same := (TaskAt.unique descriptor parent).2.2
      exact same ▸ below.trans certified.1
  | item located _ =>
      obtain ⟨path, certified, _, parentKnown⟩ := under.located located.toCurrent
      obtain ⟨_, _, _, descriptor, below⟩ := parentKnown producer rfl
      have same := (TaskAt.unique descriptor parent).2.2
      exact same ▸ below.trans certified.1

/-- A produced stream's attachment lies below its generating task's attachment.
Witness: stream navigation retains the nearest producer bound. This supplies a known
producer and a path prefix without requiring any streamed item to exist.
-/
theorem WorkUnder.stream_producer_under {base work node dependencies producer}
    (under : WorkUnder base work)
    (known : NodeAt work node .stream dependencies (some producer))
    : ∃ owners ancestor payload,
        TaskAt work producer owners ancestor payload
        ∧ payload.path.IsPrefix node.path := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | stream located =>
      obtain ⟨localPath, certified, _, parentKnown⟩ := under.located located.toCurrent
      obtain ⟨owners, ancestor, payload, task, below⟩ := parentKnown producer rfl
      exact ⟨owners, ancestor, payload, task, below.trans certified.1⟩

-----------------------------------------------------------------------------------------
-- No additional notice is needed when an ancestor report already covers the attachment
-----------------------------------------------------------------------------------------

/-- A producer's positive-error completion scope also covers its child's attachment.
Witness: generated locality and prefix transitivity, retaining the same actual report.
The child itself need not have been announced or assigned a wire ID.
-/
theorem WorkUnder.producer_reported
    {base work occurrence owners producer payload parentOwners ancestor parentPayload
      events}
    (under : WorkUnder base work)
    (known : TaskAt work occurrence owners (some producer) payload)
    (parent : TaskAt work producer parentOwners ancestor parentPayload)
    (reported : FailureReportedFor events parentPayload.path)
    : FailureReportedFor events payload.path :=
  reported.descendant (under.producer_prefix known parent)

end GraphQL.IncrementalDelivery.Correctness.ExecutionPaths
