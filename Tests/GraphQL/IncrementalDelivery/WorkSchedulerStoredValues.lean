import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemAnnotationOrder
import Tests.GraphQL.IncrementalDelivery.WorkSchedulerProducerAvailability
import Tests.GraphQL.IncrementalDelivery.WorkSchedulerStreamAvailability

/-! Source payloads survive delayed successful publication and stream-triggered draining. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerStoredValues
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated nonempty child integration uses the general event-output provenance theorem
-----------------------------------------------------------------------------------------

/-- The generated object's output retains a matching source occurrence and payload.
Witness: the general all-handler provenance theorem, not an evaluated payload assertion.
-/
theorem generated_parent_output
    : let event :=
        GraphEvent.taskSuccess WorkSchedulerProducerSupport.parentTask
          WorkSchedulerProducerSupport.result
      PublishedValuesSatisfy
        (fun occurrence value =>
          ∃ supplied,
            GraphEvent.taskSuccess occurrence supplied ∈ [event]
            ∧ supplied.value = value
            ∧ (GraphEvent.taskSuccess occurrence supplied).MatchesWork
                WorkSchedulerProducerSupport.work)
        (WorkSchedulerProducerSupport.queue.handleGraphEvent event).2 := by
  exact createWorkQueue_replay_event_publishedValues .nil _
    WorkSchedulerProducerSupport.matching

-----------------------------------------------------------------------------------------
-- A stored child value is published only after its ancestor releases it
-----------------------------------------------------------------------------------------

private def parent : DeliveryNode := { ref := 0, path := [] }
private def child : DeliveryNode := { ref := 1, path := [] }
private def stream : DeliveryNode := { ref := 2, path := [.field "items"] }
private def occurrence : Occurrence := .executionGroup [1]

private def value : ExecutionGroupValue :=
  { deliveryGroups := [child], path := [], data := [("a", .scalar "A")], errors := 2 }

/-- An internal release boundary with one earlier stored child value.
This isolates the generic drain theorem; it is not a generated/admitted source-history claim.
-/
private def before : State :=
  {
    rootGroups := [parent.ref]
    rootStreams := [stream.ref]
    registeredGroups := [parent.ref, child.ref]
    groupNodes :=
      [
        { group := ⟨parent, none⟩, childGroups := [child.ref] },
        { group := ⟨child, some parent.ref⟩, tasks := [occurrence] }
      ]
    taskNodes := [{ task := ⟨occurrence, [child]⟩, value := some value }]
    tasks := [⟨occurrence, [child]⟩]
  }

/-- The stored property records both the original occurrence and the full payload.
Witness: the single stored node includes its data, contributor descriptor, and error count.
-/
private theorem stored
    : before.StoredValuesSatisfy
        (fun source payload => source = occurrence ∧ payload = value) := by
  intro node member payload same
  have equal : node = { task := ⟨occurrence, [child]⟩, value := some value } :=
    List.mem_singleton.mp member
  subst node
  exact ⟨rfl, (Option.some.inj same).symm⟩

/-- Delayed child publication preserves its original occurrence and complete value.
Witness: the recursive drain output theorem; evaluation checks that an actual value event
occurs after the parent's child notice, so provenance is not vacuous.
-/
theorem delayed_child_provenance
    : PublishedValuesSatisfy (fun source payload => source = occurrence ∧ payload = value)
        before.drainReadyGroups.2
      ∧ before.drainReadyGroups.2
        = [
          .groupSuccess parent [child] [],
          .groupValues child [value],
          .groupSuccess child [] []
        ] := by exact ⟨stored.drainReadyGroups_outputs, by cbv⟩

private def item : StreamItem :=
  { occurrence := .item [2] 0, value := { item := .scalar "item" } }

/-- Stream processing can emit an earlier stored object value without changing its source.
Witness: the full stream-output provenance theorem and exact nonempty output, including
the original execution-error count. This remains an internal handler-boundary regression.
-/
theorem stream_triggered_object_provenance
    : PublishedValuesSatisfy (fun source payload => source = occurrence ∧ payload = value)
        (before.streamItems stream [item]).2
      ∧ (before.streamItems stream [item]).2
        = [
          .streamValues stream [item.value] [] [],
          .groupSuccess parent [child] [],
          .groupValues child [value],
          .groupSuccess child [] []
        ] := by exact ⟨stored.streamItems_outputs stream [item], by cbv⟩

-----------------------------------------------------------------------------------------
-- The same delayed publications extend a unique inventory through normalized replay
-----------------------------------------------------------------------------------------

/-- The internal stream-triggered drain publishes a fresh occurrence exactly once.
Witness: the generic inventory theorem, with exact nonempty payload erasure and residual
stored-value exclusion. This strengthens the earlier provenance-only boundary check.
-/
theorem stream_triggered_object_inventory
    : ∃ published : List ObjectPublication,
        published.map Prod.snd = [value]
        ∧ (before.streamItems stream [item]).1.PublicationInventory
            (fun source payload => source = occurrence ∧ payload = value) published := by
  have inventory : before.PublicationInventory
      (fun source payload => source = occurrence ∧ payload = value) [] :=
    ⟨by simp, by simp, stored.mono (fun _ _ known => ⟨known, by simp⟩)⟩
  obtain ⟨published, values, final⟩ := inventory.streamItems stream [item]
  have emitted : (before.streamItems stream [item]).2.flatMap WorkQueueEvent.objectValues
      = [value] := by rw [stream_triggered_object_provenance.2]; rfl
  exact ⟨published, values.trans emitted, by simpa only [List.nil_append] using final⟩

/-- Normalized generated-parent output has a unique exact source with or without empty batches.
Witness: the general normalized inventory theorem; executable output checks retain the
nonempty parent object while its child is still pending.
-/
theorem generated_parent_normalized_inventory
    : let event :=
        GraphEvent.taskSuccess WorkSchedulerProducerSupport.parentTask
          WorkSchedulerProducerSupport.result
      ∀ batches ∈ [[[event]], [[], [event], []]],
        ∃ published : List ObjectPublication,
          (published.map Prod.fst).Nodup
          ∧ published.map (fun publication => publication.2)
            = [WorkSchedulerProducerSupport.result.value]
          ∧ ∀ publication ∈ published,
              ∃ result,
                GraphEvent.taskSuccess publication.1 result ∈ batches.flatten
                ∧ result.value = publication.2
                ∧ (GraphEvent.taskSuccess publication.1 result).MatchesWork
                    WorkSchedulerProducerSupport.work := by
  dsimp only
  intro batches member
  let event := GraphEvent.taskSuccess WorkSchedulerProducerSupport.parentTask
    WorkSchedulerProducerSupport.result
  have choices : batches = [[event]] ∨ batches = [[], [event], []] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  have inputs : batches.flatten = [event] := by
    rcases choices with rfl | rfl <;> rfl
  have known : TaskAt WorkSchedulerProducerSupport.work
      WorkSchedulerProducerSupport.parentTask [WorkSchedulerProducerSupport.parent.ref] none
      (.object [] (.ok ([("user", .object [])], 0))) := by
    refine ⟨[⟨WorkSchedulerProducerSupport.parent, []⟩], [], _,
      WorkSchedulerProducerSupport.children, [], ?_, rfl, rfl⟩
    cbv
  have ready : event.Ready WorkSchedulerProducerSupport.work [] :=
    ⟨_, _, _, known, by intro source impossible; cases impossible⟩
  have valid : ValidGraphEvents WorkSchedulerProducerSupport.work [event] :=
    .append .nil WorkSchedulerProducerSupport.matching
      (by simp [event, GraphEvent.Fresh, GraphEvent.identities]) ready
  have output : (WorkSchedulerProducerSupport.queue.runNormalized batches).2.flatten.flatMap
      normalizedObjectValues = [WorkSchedulerProducerSupport.result.value] := by
    rcases choices with rfl | rfl <;> cbv
  obtain ⟨published, unique, values, sources⟩ :=
    createWorkQueue_runNormalized_objectSources (inputs ▸ valid)
  exact ⟨published, unique, values.trans output, sources⟩

/-- A generated mixed success/failure prefix has one fresh matching for objects and items.
Witness: the full normalized publication theorem, using the fixture's legal started
inputs rather than assuming output admission or constructing a matching by evaluation.
-/
theorem mixed_publication_matching
    : let outputs :=
        ((State.initialize
            (Work.fromExecution WorkSchedulerStreamRoots.work)).runNormalized
          (WorkSchedulerStreamRoots.before ++ [[WorkSchedulerStreamRoots.second]])).2
      ∃ matching : PublicationMatching,
        WorkBatching (outputs.flatten.flatMap publicationAtoms) outputs
        ∧ ∀ index event,
            (outputs.flatten.flatMap publicationAtoms)[index]? = some event
            → IsValue event
            → PublicationAt WorkSchedulerStreamRoots.work (matching index) event
              ∧ ¬Published matching
                  ((outputs.flatten.flatMap publicationAtoms).take index)
                  (matching index) := by
  apply createWorkQueue_runNormalized_publicationMatching
  · simpa only [List.flatten_append, List.flatten_singleton]
      using WorkSchedulerStreamRoots.continuation_valid
  · exact WorkSchedulerStreamRoots.inputs_started.2

/-- The mixed-prefix matching covers two real item values and a nonempty object patch.
Witness: evaluate both payload projections after the intervening deferred failure; the
unfinished second item's deferred work is retained rather than assuming termination.
-/
theorem mixed_publications_nonempty
    : let outputs :=
        ((State.initialize
            (Work.fromExecution WorkSchedulerStreamRoots.work)).runNormalized
          (WorkSchedulerStreamRoots.before
            ++ [[WorkSchedulerStreamRoots.second]])).2.flatten
      outputs.flatMap normalizedObjectValues
        = [{
            path := (WorkSchedulerStreamRoots.successGroup 0).path
            data := WorkSchedulerStreamRoots.data 0
            deliveryGroups := [WorkSchedulerStreamRoots.successGroup 0]
          }]
      ∧ outputs.flatMap normalizedItemValues
        = [
          (WorkSchedulerStreamRoots.stream, ⟨.object [], 0⟩),
          (WorkSchedulerStreamRoots.stream, ⟨.object [], 0⟩)
        ] := by
  constructor <;> cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerStoredValues
