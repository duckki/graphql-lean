import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SupportedOwnerHealth

/-! Group eligibility reduces to contents once producers and dependencies are justified. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The semantic contents check matches the implementation's two reasons to keep a notice
-----------------------------------------------------------------------------------------

/-- With producer and dependency readiness, group eligibility needs only fresh contents.
Witness: a recorded contributor failure licenses an error notice; otherwise the existing
owner-health decomposition proves health. The remaining semantic contents test is an
unaccounted task or recorded failure, not merely a nonzero implementation counter.
Relating concrete retained task memberships/error caches to these alternatives remains
an implementation proof obligation; this theorem does not add either as a source law.
-/
theorem groupNotice_canAnnounce_iff_contents
    {work initial matching events failures node dependencies producer}
    (generated : ExecutedWork work)
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : NodeAt work node .group dependencies producer)
    (produced : ∀ source, producer = some source → Published matching events source)
    (ready
      : ∀ ref ∈ dependencies,
          DependencySatisfied work initial matching events failures ref)
    : CanAnnounce work initial matching events failures node .group dependencies producer
      ↔ node.ref ∉ announcedRefs initial events
        ∧ (¬NodeAccounted work matching events failures node.ref
            ∨ HasRecordedFailure work failures events.length node.ref) := by
  constructor
  · rintro ⟨fresh, eligible, _, _⟩
    refine ⟨fresh, ?_⟩
    rcases eligible with ⟨_, stream | outstanding⟩ | ⟨_, recorded⟩
    · cases stream
    · exact .inl outstanding
    · exact .inr recorded
  · rintro ⟨fresh, contents⟩
    refine ⟨fresh, ?_, produced, ready⟩
    classical
    by_cases recorded : HasRecordedFailure work failures events.length node.ref
    · exact .inr ⟨rfl, recorded⟩
    · refine .inl ⟨?_, .inr (contents.resolve_right recorded)⟩
      intro failed
      rcases support.groupFailure_causes generated failedPayloads known produced failed with
        ⟨occurrence, owners, task, owner, member⟩ | ⟨ref, member, ancestor⟩
      · exact recorded ⟨occurrence, owners, member, task, owner⟩
      · exact (ready ref member).1 ancestor

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
