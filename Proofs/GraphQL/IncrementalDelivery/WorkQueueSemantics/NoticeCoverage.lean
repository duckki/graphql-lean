import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.NoticeFrontiers

/-! Complete eligible frontiers leave no currently eligible unannounced node.
Coverage is an existential proof witness, not an invariant required by work admission.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Compare observations differing only in their notice coverage
-----------------------------------------------------------------------------------------

/-- Every currently eligible notice is already covered: no known node can be freshly
announced from these outputs, matching, and failures. Ineligible future nodes may remain
unannounced. This property restricts a proof's construction, not public queue admission.
-/
def NoticesCovered (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failed : FailureCuts)
    : Prop :=
  ∀ node kind dependencies producer,
    NodeAt work node kind dependencies producer
    → ¬CanAnnounce work initial matching events failed node kind dependencies producer

/-- Removing notices cannot invalidate a remaining eligible notice when publications
agree and its completion and visible failure evidence are retained. Witness: transfer
freshness backwards, task accounting in both directions, and dependency satisfaction.
-/
theorem CanAnnounce.fewer_notices
    {work oldInitial initial oldMatching matching before events failed node kind
      dependencies producer}
    (eligible
      : CanAnnounce work initial matching events failed node kind dependencies producer)
    (notices : (announcedRefs oldInitial before).Subset (announcedRefs initial events))
    (publications
      : ∀ occurrence,
          Published oldMatching before occurrence ↔ Published matching events occurrence)
    (causal
      : NodeFailed work oldMatching before failed = NodeFailed work matching events failed
        ∧ TaskCancelled work oldMatching before failed
          = TaskCancelled work matching events failed)
    (completions : (completedRefs events).Subset (completedRefs before))
    (failures
      : (failedBefore failed events.length).Subset (failedBefore failed before.length))
    : CanAnnounce work oldInitial oldMatching before failed node kind dependencies
        producer := by
  have accounting (ref : NodeRef) : NodeAccounted work oldMatching before failed ref
      ↔ NodeAccounted work matching events failed ref := by
    simp only [NodeAccounted, TaskAccounted, publications, causal.2]
  have dependency {ref}
      (satisfied : DependencySatisfied work initial matching events failed ref)
      : DependencySatisfied work oldInitial oldMatching before failed ref := by
    refine ⟨by simpa only [causal.1] using satisfied.1, ?_⟩
    rcases satisfied.2 with absent | completed | ⟨unannounced, accounted⟩
    · exact Or.inl absent
    · exact Or.inr (Or.inl (completions completed))
    · exact Or.inr (Or.inr ⟨fun member => unannounced (notices member),
        (accounting ref).mpr accounted⟩)
  refine ⟨
    fun member => eligible.1 (notices member),
    ?_,
    ?_,
    ?_
  ⟩
  · rcases eligible.2.1 with ⟨healthy, outstanding⟩ | ⟨group, recorded⟩
    · exact Or.inl ⟨by simpa only [causal.1] using healthy,
        outstanding.imp_right
          (fun unaccounted accounted => unaccounted ((accounting node.ref).mp accounted))⟩
    · obtain ⟨occurrence, owners, recorded, known, owner⟩ := recorded
      exact Or.inr ⟨group, occurrence, owners, failures recorded, known, owner⟩
  · exact fun producerOccurrence same =>
      (publications producerOccurrence).mpr
        (eligible.2.2.1 producerOccurrence same)
  · cases kind with
    | group => exact fun ref member => dependency (eligible.2.2.2 ref member)
    | stream =>
        rcases eligible.2.2.2 with empty | ⟨ref, member, satisfied⟩
        · exact Or.inl empty
        · exact Or.inr ⟨ref, member, dependency satisfied⟩

-----------------------------------------------------------------------------------------
-- Covering initialization and actual notice-bearing events
-----------------------------------------------------------------------------------------

/-- A covering initial frontier leaves no eligible node unannounced. Witness: any
remaining eligible descriptor was also eligible before adding these initial notices,
contradicting the frontier's coverage. No later publication matching is selected.
-/
theorem NoticesCovered.initial {work} {groups streams : List DeliveryNode}
    (covers
      : ∀ node kind dependencies birth,
          NodeAt work node kind dependencies birth
          → CanAnnounce work [] (fun _ => .executionGroup []) [] [] node kind dependencies
              birth
          → node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
    (matching : PublicationMatching)
    : NoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching [] [] := by
  intro node kind dependencies birth known eligible
  have before := eligible.fewer_notices
    (oldInitial := []) (oldMatching := fun _ => .executionGroup []) (before := [])
    (by intro ref member; simp [announcedRefs, pendingRefs] at member)
    (by simp [Published])
    (by constructor <;> funext ref <;> simp [NodeFailed, TaskCancelled])
    (List.Subset.refl _)
    (List.Subset.refl _)
  apply eligible.1
  simpa [announcedRefs, pendingRefs]
    using covers node kind dependencies birth known before

/-- A covering carrier leaves no eligible node unannounced after its actual notices.
Witness: remove just the carrier's notices while preserving publications and completions;
the supplied complete frontier then contradicts the node's claimed freshness.
-/
theorem NoticesCovered.carrier {work initial matching events failed plain actual}
    {groups streams : List DeliveryNode} (noNotices : eventPending plain = [])
    (notices : eventPending actual = (groups ++ streams).map DeliveryNode.ref)
    (sameValue : IsValue plain ↔ IsValue actual)
    (sameCompleted : eventCompleted plain = eventCompleted actual)
    (covers
      : ∀ node kind dependencies birth,
          NodeAt work node kind dependencies birth
          → CanAnnounce work initial matching (events ++ [plain]) failed
              node kind dependencies birth
          → node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
    : NoticesCovered work initial matching (events ++ [actual]) failed := by
  intro node kind dependencies birth known eligible
  have snapshots (cut : Nat) :
      Published matching ((events ++ [plain]).take cut)
        = Published matching ((events ++ [actual]).take cut) := by
    by_cases earlier : cut ≤ events.length
    · simp only [List.take_append_of_le_length earlier]
    · have plainBound : (events ++ [plain]).length ≤ cut := by
        simp only [List.length_append, List.length_singleton]; omega
      have actualBound : (events ++ [actual]).length ≤ cut := by
        simp only [List.length_append, List.length_singleton]; omega
      simp only [List.take_of_length_le plainBound, List.take_of_length_le actualBound]
      funext occurrence
      apply propext
      simp only [published_append_singleton_iff, sameValue]
  have causal :
      NodeFailed work matching (events ++ [plain]) failed
        = NodeFailed work matching (events ++ [actual]) failed
      ∧ TaskCancelled work matching (events ++ [plain]) failed
        = TaskCancelled work matching (events ++ [actual]) failed := by
    constructor <;> funext ref <;>
      simp only [NodeFailed, TaskCancelled, List.length_append, List.length_singleton,
        snapshots]
  have before :=
    eligible.fewer_notices
      (oldInitial := initial)
      (oldMatching := matching)
      (before := events ++ [plain])
      (by
        simp only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, noNotices]
        intro ref member
        simpa only [List.append_assoc]
          using List.mem_append_left (eventPending actual) member)
      (by intro occurrence; simp only [published_append_singleton_iff, sameValue])
      causal
      (by
        simp only [completedRefs, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, sameCompleted]
        exact List.Subset.refl _)
      (by simp only [List.length_append, List.length_singleton]; exact List.Subset.refl _)
  apply eligible.1
  have member := covers node kind dependencies birth known before
  simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc, notices]
    using List.mem_append_right (announcedRefs initial events) member

/-- A ready stream item can publish while covering every currently eligible notice.
Witness: the existing covering-frontier construction, followed by carrier coverage.
-/
theorem Explains.publish_item_noticesCovered
    {work groups streams events matching failures occurrence owners producer node item
      errors}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer (.item node (.ok (item, errors))))
    (ready : CanPublish work matching events failures occurrence producer)
    (owner
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures owners node)
    : ∃ newGroups newStreams,
        Explains work groups streams
          (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
          (matchNext matching events.length occurrence) failures
        ∧ NoticesCovered work ((groups ++ streams).map DeliveryNode.ref)
            (matchNext matching events.length occurrence)
            (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
            failures := by
  obtain ⟨newGroups, newStreams, extended, covers⟩ :=
    explained.publish_item_covering known ready owner
  refine ⟨newGroups, newStreams, extended, ?_⟩
  exact NoticesCovered.carrier (plain := .streamValues node [{ item, errors }] [] [])
    rfl rfl Iff.rfl rfl covers

/-- An open healthy accounted group can close while covering all currently eligible
notices. Witness: the covering group-success event and the same carrier coverage lemma.
-/
theorem Explains.complete_group_noticesCovered
    {work groups streams events matching failures node dependencies birth}
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies birth)
    (opened : Open ((groups ++ streams).map DeliveryNode.ref) events node.ref)
    (healthy : ¬NodeFailed work matching events failures node.ref)
    (accounted : NodeAccounted work matching events failures node.ref)
    : ∃ newGroups newStreams,
        Explains work groups streams (events ++ [.groupSuccess node newGroups newStreams])
          matching failures
        ∧ NoticesCovered work ((groups ++ streams).map DeliveryNode.ref) matching
            (events ++ [.groupSuccess node newGroups newStreams])
            failures := by
  obtain ⟨newGroups, newStreams, extended, covers⟩ :=
    explained.complete_group_covering known opened healthy accounted
  refine ⟨newGroups, newStreams, extended, ?_⟩
  exact NoticesCovered.carrier (plain := .groupSuccess node [] [])
    rfl rfl Iff.rfl rfl covers

end GraphQL.IncrementalDelivery.WorkQueueSemantics
