import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.NoticeFrontiers
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureExtension

/-! Proof-only coverage of parentless stream notices. A complete frontier on each chosen
item publication supplies this witness; it is not a new condition on admitted histories.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Notice coverage retained by the existential construction
-----------------------------------------------------------------------------------------

/-- Every healthy parentless stream with a published producer has already been announced.
The matching and failure list describe the supplied output prefix, not future work.
-/
def ParentlessStreamsNotified (work : Work) (initial : Keys)
    (matching : PublicationMatching) (events : List WorkEvent) (failed : List Occurrence)
    : Prop :=
  ∀ node producer,
    NodeAt work node .stream [] producer
    → (∀ parent, producer = some parent → Published matching events parent)
    → ¬NodeFailed work failed node.key
    → node.key ∈ announcedKeys initial events

/-- A covering initial frontier includes every ready parentless stream. Witness:
its producer publication and unconditional stream eligibility license the notice.
-/
theorem ParentlessStreamsNotified.initial {work} {groups streams : List DeliveryNode}
    (covers
      : ∀ node kind parents birth,
          NodeAt work node kind parents birth
          → CanAnnounce work [] (fun _ => .deferred []) [] [] node kind parents birth
          → node.key ∈ (groups ++ streams).map DeliveryNode.key)
    : ParentlessStreamsNotified work ((groups ++ streams).map DeliveryNode.key)
        (fun _ => .deferred []) [] [] := by
  intro node producer known ready healthy
  simpa only [announcedKeys, pendingKeys, List.flatMap_nil, List.append_nil]
    using covers node .stream [] producer known
      ⟨by simp [announcedKeys, pendingKeys], healthy, Or.inl rfl, ready, Or.inl rfl⟩

/-- A control event cannot create a new producer publication or healthy stream.
Witness: invert its publication lookup and transport health to the smaller failure list.
-/
theorem ParentlessStreamsNotified.append_control
    {work initial matching events failed more event}
    (notified : ParentlessStreamsNotified work initial matching events failed)
    (control : ¬IsValue event) (included : failed ⊆ more)
    : ParentlessStreamsNotified work initial matching (events ++ [event]) more := by
  intro node producer known ready healthy
  have earlier : ∀ parent, producer = some parent → Published matching events parent := by
    intro parent same
    rcases published_append_singleton_iff.mp (ready parent same) with old | new
    · exact old
    · exact False.elim (control new.1)
  have member := notified node producer known earlier
    (fun failure => healthy (failure.mono included))
  simpa only [announcedKeys, pendingKeys, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]
    using List.mem_append_left (eventPending event) member

-----------------------------------------------------------------------------------------
-- Successful item publications install all currently ready parentless notices
-----------------------------------------------------------------------------------------

/-- A stream item can publish while covering all healthy parentless streams then ready.
Witness: the complete eligible frontier, with publication lookup unchanged by attaching
its notices. This can introduce arbitrarily many nested stream keys on the same event.
-/
theorem Explains.publish_item_notified
    {work groups streams events matching failures occurrence owners producer node item
      errors}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer (.item node (.ok (item, errors))))
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    (selected
      : Owner work ((groups ++ streams).map DeliveryNode.key) events
          (failedBefore failures events.length) owners node)
    : ∃ newGroups newStreams,
        Explains work groups streams
          (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
          (matchNext matching events.length occurrence) failures
        ∧ ParentlessStreamsNotified work ((groups ++ streams).map DeliveryNode.key)
            (matchNext matching events.length occurrence)
            (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
            (failures.map Prod.snd) := by
  classical
  obtain ⟨newGroups, newStreams, extended, covers⟩ :=
    explained.publish_item_covering known ready selected
  refine ⟨newGroups, newStreams, extended, ?_⟩
  intro child birth descriptor produced healthy
  by_cases old :
    child.key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events
  · simpa only [announcedKeys, pendingKeys, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc]
      using List.mem_append_left
        (eventPending (.streamValues node [{ item, errors }] newGroups newStreams)) old
  · have eligible : CanAnnounce work ((groups ++ streams).map DeliveryNode.key)
        (matchNext matching events.length occurrence)
        (events ++ [.streamValues node [{ item, errors }] [] []])
        (failedBefore failures events.length) child .stream [] birth := by
      refine ⟨?_, ?_, Or.inl rfl, ?_, Or.inl rfl⟩
      · simpa [announcedKeys, pendingKeys, eventPending] using old
      · simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)] using healthy
      · intro parent same
        simpa only [published_append_singleton_iff, IsValue] using produced parent same
    have added := covers child .stream [] birth descriptor eligible
    simpa only [announcedKeys, pendingKeys, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, eventPending]
      using List.mem_append_right
        (announcedKeys ((groups ++ streams).map DeliveryNode.key) events) added

end GraphQL.IncrementalDelivery.WorkScheduler
