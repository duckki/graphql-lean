import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.NoticeFrontiers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureExtension

/-! Proof-only coverage of dependency-free stream notices. A complete frontier on each
chosen item publication supplies this witness; it is not a new condition on admitted
histories.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Notice coverage retained by the existential construction
-----------------------------------------------------------------------------------------

/-- Every healthy dependency-free stream with a published producer has already been
announced. The matching and failure list describe the supplied output prefix, not future
work.
-/
def DependencyFreeStreamsNotified (work : Work) (initial : NodeRefs)
    (matching : PublicationMatching) (events : List WorkQueueEvent) (failed : FailureCuts)
    : Prop :=
  ∀ node producer,
    NodeAt work node .stream [] producer
    → (∀ source, producer = some source → Published matching events source)
    → ¬NodeFailed work matching events failed node.ref
    → node.ref ∈ announcedRefs initial events

/-- A covering initial frontier includes every ready dependency-free stream. Witness:
its producer publication and unconditional stream eligibility license the notice.
-/
theorem DependencyFreeStreamsNotified.initial {work} {groups streams : List DeliveryNode}
    (covers
      : ∀ node kind dependencies birth,
          NodeAt work node kind dependencies birth
          → CanAnnounce work [] (fun _ => .executionGroup []) [] [] node kind dependencies
              birth
          → node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
    : DependencyFreeStreamsNotified work ((groups ++ streams).map DeliveryNode.ref)
        (fun _ => .executionGroup []) [] [] := by
  intro node producer known ready healthy
  simpa only [announcedRefs, pendingRefs, List.flatMap_nil, List.append_nil]
    using covers node .stream [] producer known
      ⟨
        by simp [announcedRefs, pendingRefs],
        Or.inl ⟨healthy, Or.inl rfl⟩,
        ready,
        Or.inl rfl
      ⟩

/-- A control event cannot create a new producer publication or healthy stream.
Witness: invert its publication lookup and transport health to the smaller failure list.
-/
theorem DependencyFreeStreamsNotified.append_control
    {work initial matching events failed more event}
    (notified : DependencyFreeStreamsNotified work initial matching events failed)
    (control : ¬IsValue event) (included : failed ⊆ more)
    : DependencyFreeStreamsNotified work initial matching (events ++ [event]) more := by
  intro node producer known ready healthy
  have earlier : ∀ source, producer = some source → Published matching events source := by
    intro source same
    rcases published_append_singleton_iff.mp (ready source same) with old | new
    · exact old
    · exact False.elim (control new.1)
  have member := notified node producer known earlier
    (fun failure => healthy ((failure.mono included).append [event]))
  simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]
    using List.mem_append_left (eventPending event) member

-----------------------------------------------------------------------------------------
-- Successful item publications install all currently ready dependency-free notices
-----------------------------------------------------------------------------------------

/-- A stream item can publish while covering all healthy dependency-free streams then
ready. Witness: the complete eligible frontier, with publication lookup unchanged by
attaching its notices. This can introduce arbitrarily many nested stream refs on the same
event.
-/
theorem Explains.publish_item_notified
    {work groups streams events matching failures occurrence owners producer node item
      errors}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer (.item node (.ok (item, errors))))
    (ready : CanPublish work matching events failures occurrence producer)
    (selected
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures owners node)
    : ∃ newGroups newStreams,
        Explains work groups streams
          (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
          (matchNext matching events.length occurrence) failures
        ∧ DependencyFreeStreamsNotified work ((groups ++ streams).map DeliveryNode.ref)
            (matchNext matching events.length occurrence)
            (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
            failures := by
  classical
  obtain ⟨newGroups, newStreams, extended, covers⟩ :=
    explained.publish_item_covering known ready selected
  refine ⟨newGroups, newStreams, extended, ?_⟩
  intro child birth descriptor produced healthy
  by_cases old :
    child.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
  · simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc]
      using List.mem_append_left
        (eventPending (.streamValues node [{ item, errors }] newGroups newStreams)) old
  · have eligible : CanAnnounce work ((groups ++ streams).map DeliveryNode.ref)
        (matchNext matching events.length occurrence)
        (events ++ [.streamValues node [{ item, errors }] [] []])
        failures child .stream [] birth := by
      refine ⟨?_, Or.inl ⟨?_, Or.inl rfl⟩, ?_, Or.inl rfl⟩
      · simpa [announcedRefs, pendingRefs, eventPending] using old
      · simpa only [(causality_carrier_eq (work := work) (failures := failures)
          (matching := matchNext matching events.length occurrence)
          (events := events) (left := .streamValues node [{ item, errors }] [] [])
          (right := .streamValues node [{ item, errors }] newGroups newStreams)
          Iff.rfl).1] using healthy
      · intro source same
        simpa only [published_append_singleton_iff, IsValue] using produced source same
    have added := covers child .stream [] birth descriptor eligible
    simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, eventPending]
      using List.mem_append_right
        (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events) added

end GraphQL.IncrementalDelivery.WorkQueueSemantics
